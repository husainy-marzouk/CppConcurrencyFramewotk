#include <chrono>
#include <condition_variable>
#include <cstddef>
#include <future>
#include <iostream>
#include <limits>
#include <memory>
#include <mutex>
#include <new>
#include <queue>
#include <random>
#include <stdexcept>
#include <thread>
#include <variant>
#include <vector>
#include <optional>
#include <atomic>
#include <functional>
#include <cstdlib>
#include <utility>
#include <tuple>
#include <numeric>

// ------------------ HierarchicalMutex ------------------
class HierarchicalMutex {
    std::mutex internalMutex;
    unsigned long const hierarchyValue;
    unsigned long previousHierarchyValue;
    static thread_local unsigned long threadHierarchyValue;

    void checkHierarchyViolation() {
        if (threadHierarchyValue <= hierarchyValue) {
            throw std::logic_error("Mutex hierarchy violated");
        }
    }

    void updateHierarchyValue() {
        previousHierarchyValue = threadHierarchyValue;
        threadHierarchyValue = hierarchyValue;
    }

public:
    explicit HierarchicalMutex(unsigned long value)
        : hierarchyValue(value), previousHierarchyValue(0) {}

    void lock() {
        checkHierarchyViolation();
        internalMutex.lock();
        updateHierarchyValue();
    }

    void unlock() {
        threadHierarchyValue = previousHierarchyValue;
        internalMutex.unlock();
    }

    bool try_lock() {
        checkHierarchyViolation();
        if (!internalMutex.try_lock())
            return false;
        updateHierarchyValue();
        return true;
    }
};

thread_local unsigned long HierarchicalMutex::threadHierarchyValue(std::numeric_limits<unsigned long>::max());

// ------------------ ThreadSafeQueue ------------------
template <typename T>
class ThreadSafeQueue {
    std::atomic<bool> isShutdown;
    std::queue<T> taskQueue;
    std::mutex queueMutex;
    std::condition_variable conditionVar;

public:
    ThreadSafeQueue() : isShutdown(false) {}

    ThreadSafeQueue(const ThreadSafeQueue& other) = delete;
    ThreadSafeQueue& operator=(const ThreadSafeQueue& other) = delete;

    void push(const T& value) noexcept {
        {
            std::lock_guard<std::mutex> lock(queueMutex);
            taskQueue.push(value);
        }
        conditionVar.notify_one();
    }

    std::optional<T> pop(std::chrono::milliseconds timeout) noexcept {
        std::unique_lock<std::mutex> lock(queueMutex);
        if (!conditionVar.wait_for(lock, timeout, [this]() { return !taskQueue.empty() || isShutdown; }))
            return std::nullopt;
        if (taskQueue.empty())
            return std::nullopt;
        T res = std::move(taskQueue.front());
        taskQueue.pop();
        return res;
    }

    template <typename... Args>
    void emplace(Args&&... args) {
        {
            std::lock_guard<std::mutex> lock(queueMutex);
            taskQueue.emplace(std::forward<Args>(args)...);
        }
        conditionVar.notify_one();
    }

    void shutdown() noexcept {
        isShutdown.store(true);
        conditionVar.notify_all();
    }
};

// ------------------ ThreadPool ------------------
class ThreadPool {
    ThreadSafeQueue<std::function<void()>> taskQueue;
    std::vector<std::thread> workerThreads;
    std::atomic<bool> isShutdown;

public:
    explicit ThreadPool(unsigned long numThreads) : isShutdown(false) {
        for (unsigned long i = 0; i < numThreads; ++i) {
            workerThreads.emplace_back([this]() {
                while (true) {
                    auto task = taskQueue.pop(std::chrono::milliseconds(100));
                    if (!task.has_value() && isShutdown.load()) {
                        return;
                    }
                    if (task) {
                        (*task)();
                    }
                }
            });
        }
    }

    template <typename Func, typename... Args>
    auto submit(Func&& func, Args&&... args) -> std::future<decltype(func(args...))> {
        using ReturnType = decltype(func(args...));
        auto task = std::make_shared<std::packaged_task<ReturnType()>>(
            std::bind(std::forward<Func>(func), std::forward<Args>(args)...));
        std::future<ReturnType> future = task->get_future();
        taskQueue.push([task]() { (*task)(); });
        return future;
    }

    void shutdown() {
        isShutdown.store(true);
        taskQueue.shutdown();
    }

    ~ThreadPool() {
        shutdown();
        for (auto& thread : workerThreads)
            if (thread.joinable())
                thread.join();
    }
};

// ------------------ memory_pool ------------------
class memory_pool {
public:
    explicit memory_pool(void* ptr, std::size_t size)
        : pool_(static_cast<std::byte*>(ptr)), pool_size_(size), offset_(0), free_list_(nullptr),
          alloc_count_(0), free_count_(0) { }

    void* allocate(std::size_t block_size) noexcept {
        if (block_size == 0) return nullptr;

        BlockHeader* prev = nullptr;
        BlockHeader* curr = free_list_;
        while (curr) {
            if (curr->blockSize >= block_size) {
                if (prev) {
                    prev->next = curr->next;
                } else {
                    free_list_ = curr->next;
                }
                ++alloc_count_;
                return static_cast<void*>(curr + 1);
            }
            prev = curr;
            curr = curr->next;
        }

        if (offset_ + sizeof(BlockHeader) + block_size > pool_size_) {
            std::cerr << "Allocation failed: Not enough memory available.\n";
            return nullptr;
        }
        std::byte* addr = pool_ + offset_;
        BlockHeader* header = new (addr) BlockHeader();
        header->blockSize = block_size;
        offset_ += sizeof(BlockHeader) + block_size;
        ++alloc_count_;
        return static_cast<void*>(header + 1);
    }
    
    void release(void* ptr) noexcept {
        if (!ptr) return;
        BlockHeader* header = reinterpret_cast<BlockHeader*>(ptr) - 1;
        if (!free_list_) {
            free_list_ = header;
            ++free_count_;
            return;
        }
        BlockHeader* prev = nullptr;
        BlockHeader* curr = free_list_;
        while (curr && curr < header) {
            prev = curr;
            curr = curr->next;
        }
        if (curr && (reinterpret_cast<std::byte*>(header) + sizeof(BlockHeader) + header->blockSize == reinterpret_cast<std::byte*>(curr))) {
            header->blockSize += sizeof(BlockHeader) + curr->blockSize;
            header->next = curr->next;
        } else {
            header->next = curr;
        }
        if (prev && (reinterpret_cast<std::byte*>(prev) + sizeof(BlockHeader) + prev->blockSize == reinterpret_cast<std::byte*>(header))) {
            prev->blockSize += sizeof(BlockHeader) + header->blockSize;
            prev->next = header->next;
        } else {
            if (prev) {
                prev->next = header;
            } else {
                free_list_ = header;
            }
        }
        ++free_count_;
    }

    std::size_t available() const noexcept {
        return pool_size_ - offset_;
    }
    
    void reset() noexcept {
        offset_ = 0;
        free_list_ = nullptr;
        alloc_count_ = 0;
        free_count_ = 0;
    }

    void debug_print() const noexcept {
        std::cout << "Memory Pool Debug Info:\n";
        std::cout << "  Total Size: " << pool_size_ << " bytes\n";
        std::cout << "  Used: " << offset_ << " bytes\n";
        std::cout << "  Available: " << available() << " bytes\n";
        std::cout << "  Allocations: " << alloc_count_ << "\n";
        std::cout << "  Frees: " << free_count_ << "\n";

        BlockHeader* curr = free_list_;
        std::cout << "  Free Blocks:\n";
        while (curr) {
            std::cout << "    [Size: " << curr->blockSize << "]\n";
            curr = curr->next;
        }
    }

private:
  
    struct alignas(std::max_align_t) BlockHeader {
        std::size_t blockSize;
        BlockHeader* next;
        BlockHeader() : blockSize(0), next(nullptr) {}
    };

    std::byte* pool_;
    std::size_t pool_size_;
    std::size_t offset_;
    BlockHeader* free_list_;

    std::size_t alloc_count_;
    std::size_t free_count_;
};

void test_memory_pool_merging(memory_pool& pool) {
    std::cout << "\nStarting memory_pool merging test...\n";
    void* a = pool.allocate(100);
    void* b = pool.allocate(150);
    void* c = pool.allocate(200);
    if (!a || !b || !c) {
        std::cerr << "Allocation failed during merging test.\n";
        return;
    }
    std::cout << "After allocation:\n";
    pool.debug_print();

    pool.release(a);
    pool.release(c);
    std::cout << "\nAfter releasing blocks a (100 bytes) and c (200 bytes):\n";
    pool.debug_print();

    pool.release(b);
    std::cout << "\nAfter releasing block b (150 bytes):\n";
    pool.debug_print();

    pool.reset();
    std::cout << "\nAfter resetting memory_pool:\n";
    pool.debug_print();
}


std::mutex poolMutex;

void task_using_memory_pool(memory_pool& pool, int taskId, std::size_t allocSize) {
    void* mem = nullptr;
    {
        std::lock_guard<std::mutex> lock(poolMutex);
        mem = pool.allocate(allocSize);
        std::cout << "Task " << taskId << ": allocated " << allocSize << " bytes.\n";
        pool.debug_print();
        if (!mem) {
            std::cout << "Task " << taskId << ": allocation failed.\n";
            return;
        }
    }
    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    {
        std::lock_guard<std::mutex> lock(poolMutex);
        pool.release(mem);
        std::cout << "Task " << taskId << ": freed memory.\n";
        pool.debug_print();
    }
}


HierarchicalMutex highLevel(10000);
HierarchicalMutex midLevel(5000);
HierarchicalMutex lowLevel(1000);

class hybrid_hierarchical_pool : public ThreadPool, public memory_pool {
public:
    hybrid_hierarchical_pool(unsigned long hardware_cores, void* ptr, const std::size_t size)
        : ThreadPool(hardware_cores), memory_pool(ptr, size) {}
        
    template <typename Fun, typename... Args>
    auto task_hierarchical_mutex(Fun&& fun, Args&&... args) -> std::future<decltype(fun(args...))> {
      
        using ReturnType = decltype(fun(args...));
        auto args_tuple = std::make_tuple(std::forward<Args>(args)...);
        auto taskLambda = [this, fun = std::forward<Fun>(fun), args_tuple]() -> ReturnType {
            std::lock_guard<HierarchicalMutex> lk(highLevel);
            void* mem = allocate(sizeof(ReturnType));
            if (!mem)
                throw std::bad_alloc();
            ReturnType* resultPtr = new (mem) ReturnType(std::apply(fun, args_tuple));
            ReturnType result = *resultPtr;
            resultPtr->~ReturnType();
            release(mem);
            return result;
        };
        
        return submit(taskLambda);
    }
};

int main() {
    constexpr std::size_t pool_size = 1024;
    auto memory = std::make_unique<std::byte[]>(pool_size);

    unsigned long num_threads = std::thread::hardware_concurrency();
    if (num_threads == 0) {
        num_threads = 2;
    }

    hybrid_hierarchical_pool hybridPool(num_threads, memory.get(), pool_size);

    auto futureResult = hybridPool.task_hierarchical_mutex([](int a, int b) -> int {
        return a + b;
    }, 7, 3);

    int result = futureResult.get();
    std::cout << "Result: " << result << std::endl;

    std::this_thread::sleep_for(std::chrono::seconds(1));

    hybridPool.shutdown();

    return 0;
}
