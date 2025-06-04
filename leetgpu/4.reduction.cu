// URL: https://leetgpu.com/challenges/reduction
// GPU: NVIDIA TESLA T4
// Runtime: 4.11309 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <iostream>

__global__ void sum(const float* input, float* output, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        sharedMem[threadIdx.x] = input[idx];
    } else {
        sharedMem[threadIdx.x] = 0.0;
    }
    __syncthreads();
    //approach is to add each shift-rd element
    int shift_tid = threadIdx.x + 1;
    for (int shift = 1; shift < blockDim.x; shift <<= 1) {//all threads should have same amount iterations to avoid from conditional __syncthreads
        if(shift_tid < blockDim.x) {
            sharedMem[shift_tid - shift] += sharedMem[shift_tid];
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.x == 0) {
        atomicAdd(output,sharedMem[0]);
    }
}

// input, output are device pointers
void solve(const float* input, float* output, int N) {  
    const int threadsPerBlock = 1024;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    sum<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(input, output, N);
    cudaDeviceSynchronize();  
}
