// URL: https://leetgpu.com/challenges/prefix-sum
// GPU: NVIDIA TESLA T4
// Runtime: 0.12229 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <cooperative_groups.h>

// to perform computation by using warp level sata transfer mechanisms, each thread 
// always need to change its dedicated memory and can not read variables of other threads 
// and atomically write into variable of another thread
// if in some point of time, we have buckets with size bucketDim 
// then threads of every second bucket should add last elem of previous bucket
// bucketId of given thread is threadIdx.x/bucketDim, last elem of previous bucket is bucketId*bucketDim-1
// thread should add this elem only if bucketId%2==1
// we can use masks to include only threads of every second bucket
// or we can try to make so that calulation of last elem of previous bucket will return out of bound value for previous buckets of every second bucket
// at the begining mask should be 0xAAAAAAAA (same as ... 1010 1010)  
// in second iteration it should be 0xCCCCCCCC (same as ... 1100 1100)
// for out of bound threads, shfl will return val of current thread, so we need to multiply it by 0 in this case, and there is no need for masks 


constexpr int threadsPerBlock = 512;

namespace cg = cooperative_groups;

__global__ void prefix_sum(const float* input, float* output, int N) {
    constexpr int warpSize = 32;
    constexpr int numWarpsPerBlock = threadsPerBlock / warpSize;

    __shared__ float warp_last[numWarpsPerBlock];// last elements of outputs of each warp

    const auto idx = blockIdx.x * threadsPerBlock + threadIdx.x;

    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<warpSize> warp = cg::tiled_partition<warpSize>(block);
    const auto lane_id = warp.thread_rank();

    float val;
    if(idx < N) {
        val = input[idx];
    } else {
        val = 0.0f;
    }
    #pragma unroll
    for (int bucketDim = 1; 2*bucketDim <= warpSize; bucketDim *= 2) {
        const int bucketId = lane_id/bucketDim;
        const int prev_bucket_elem = bucketId*bucketDim-1;
        const int is_active_bucket = -(bucketId % 2);
        val += __int_as_float(is_active_bucket & __float_as_int(warp.shfl(val, prev_bucket_elem)));
    }

    #pragma unroll
    for (int bucketDim = warpSize; 2*bucketDim <= threadsPerBlock; bucketDim *= 2) {
        const int bucketId = threadIdx.x/bucketDim;
        if(threadIdx.x % bucketDim == (bucketDim-1)) { // last thread of each bucket
            warp_last[bucketId] = val;
        }
        block.sync();

        if(bucketId % 2 == 1) {
            val += warp_last[bucketId - 1];
        }
        block.sync();
    }

    if(idx < N) {
        output[idx] = val;
    }
}

__global__ void merge_prefix_sums_of_blocks(const float* input, float* output, int N, int groupDim) {
    __shared__ float last_sum;
    const int idx = blockIdx.x * blockDim.x + threadIdx.x;
    const int tid = idx/groupDim;
    const int out_index = groupDim*(tid+1) + idx;
    if(threadIdx.x == 0) {
        last_sum = output[groupDim*(2*tid+1)-1];//reading from output(stored in global memory) only one time 
    }
    __syncthreads();
    if(out_index < N) {
        output[out_index] += last_sum;
    }
}


// input, output are device pointers
void solve(const float* input, float* output, int N) {
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    prefix_sum<<<blocksPerGrid, threadsPerBlock>>>(input, output, N);
    cudaDeviceSynchronize(); 
    int groupDim = threadsPerBlock;
    for (;;) {
        // in worst case we will have (N+groupDim-1)/groupDim groups
        // but only half of them are needed
        int numThreads = groupDim*(((N+groupDim-1)/groupDim)/2);
        if(numThreads < 1) {
            break;
        }
        int blocksPerGrid = (numThreads + threadsPerBlock - 1) / threadsPerBlock;
        merge_prefix_sums_of_blocks<<<blocksPerGrid, threadsPerBlock>>>(input, output, N, groupDim);
        cudaDeviceSynchronize(); 
        groupDim *= 2;
    } 
} 
