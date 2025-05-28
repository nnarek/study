// URL: https://leetgpu.com/challenges/prefix-sum
// GPU: NVIDIA TESLA T4
// Runtime: 0.13922 ms
#include "solve.h"
#include <cuda_runtime.h>

// first i have solved problem by dynamic programming
// we can use half of threads to solve problem for first half of array and also use other threads for second half. 
// after that we need to add last element of first half to all elements of second half
// now we need to implement this using loops, also we need to do almost same with results of each block
// 0->1 2->3 4->5 
// sharedMem[2*threadIdx.x+1] += sharedMem[2*threadIdx.x];

//   0    1   2    3   ... threads ids
// 1->2 1->3 5->6 5->7   ... should be added from->to by corresponding thread
// sharedMem[2*(1+threadIdx.x/2)+threadIdx.x] += sharedMem[4*(threadIdx.x/2)+1];

// in general after n iteration we will have solved subarray with size 2^n(note that last subarray can have less size than 2^n)
// and each time we need to add last element of first subarray to all elements of second subarrat, and do same for 3rd,5th ... subarrays
// hence tid-rd thread should add to all elements of 2*(tid/2^n)+1 subarray, which first element is located at 2^n*(2*(tid/2^n)+1)
// and each of that threads should add value from element with index 2^n*(2*(tid/2^n)+1)-1
// local index of given thread within its group is tid%2^n
// so we need to do folowing on each iteration
// shMem[2^n*(2*(tid/2^n)+1) + tid%2^n] += shMem[2^n*(2*(tid/2^n)+1)-1]
// which can be simplified to 
// shMem[2^n*(tid/2^n)+2^n + tid] += shMem[2^n*(2*(tid/2^n)+1)-1]

// in the level of block we have same problem but in this case group size is bigger or equal to threadsPerBlock, so we can try to reuse code

const int threadsPerBlock = 1024;

__global__ void prefix_sum(const float* input, float* output, int N) {
    __shared__ float shMem[threadsPerBlock];

    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if(idx >= N) {
        return;
    }
    shMem[threadIdx.x] = input[idx];

    int tid = threadIdx.x;
    int groupDim = 1;
    __syncthreads();
    while (true) {
        const int out_index = groupDim*(tid+1) + threadIdx.x;
        if(out_index < threadsPerBlock) {
            shMem[out_index] += shMem[groupDim*(2*tid+1)-1];
        }
        tid /= 2;
        groupDim *= 2;
        __syncthreads();
        if(groupDim >= threadsPerBlock) {
            break;
        }
    }
    __syncthreads();

    output[idx] = shMem[threadIdx.x];
}

__global__ void merge_prefix_sums_of_blocks(const float* input, float* output, int N, int groupDim) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int tid = idx/groupDim;
    int out_index = groupDim*(tid+1) + idx;
    if(out_index < N) {
        output[out_index] += output[groupDim*(2*tid+1)-1];
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
