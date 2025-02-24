#ifndef HYRAX_DEFINE
#define HYRAX_DEFINE
#include <iostream>
#include <vector>
#include <queue>
#include <mutex>
#include <condition_variable>
#include <thread>         // std::thread
#include <mcl/bn256.hpp>
#include "timer.hpp"
#include "typedef.hpp"
using namespace std;
using namespace mcl::bn;

struct Pack 
{
    G1 gamma;
    Fr a;
    G1 g;
    Fr x;
    Fr y;
    
    Pack(G1 gamm,Fr fa, G1 gg,Fr xx,Fr yy)
    {
        gamma=gamm;
        a=fa;
        g=gg;
        x=xx;
        y=yy;
    }
};

G1 perdersen_commit(G1* g,ll* f,int n,G1* W=NULL); //support 2^80, optimized using pippenger
Fr lagrange(Fr *r,int l,int k);


G1 gen_gi(G1* g,int n);

bool prove_dot_product(G1 comm_x, G1 comm_y, Fr* a, Fr* x,Fr y, G1*g ,G1& G,int n);

G1* prover_commit(ll* w, G1* g, int l,int thread_n=1);
Fr prover_evaluate(ll*w ,Fr*r,int l);  // nlogn brute force 
void open(ll*w,Fr*r,Fr eval,G1&G,G1*g,G1*comm,int l);


template <typename T>
class ThreadSafeQueue {
public:
    ThreadSafeQueue() {}

    void Push(T value) {
        unique_lock<mutex> lock(mutex_);
        queue_.push(value);
        lock.unlock();
        condition_variable_.notify_one();
    }

    bool TryPop(T& value) {
        lock_guard<mutex> lock(mutex_);
        if (queue_.empty()) {
            return false;
        }
        value = queue_.front();
        queue_.pop();
        return true;
    }

    void WaitPop(T& value) {
        unique_lock<mutex> lock(mutex_);
        condition_variable_.wait(lock, [this] { return !queue_.empty(); });
        value = queue_.front();
        queue_.pop();
    }

    bool Empty() const {
        lock_guard<mutex> lock(mutex_);
        return queue_.empty();
    }
    int Size() const {
        lock_guard<mutex> lock(mutex_);
        return queue_.size();
    }
    void Clear()  
    {
        lock_guard<mutex> lock(mutex_);
        queue_={};
    }

private:
    mutable mutex mutex_;
    queue<T> queue_;
    condition_variable condition_variable_;
};

#endif
