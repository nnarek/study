// URL: https://leetgpu.com/challenges/reduction
// GPU: NVIDIA TESLA T4
// Runtime: 2.28479 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <iostream>

const int threadsPerBlock = 1024;

__global__ void sum(const float* input, float* output, int N) {
    __shared__ float sharedMem[threadsPerBlock];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx >= N) {
        return;
    }
    sharedMem[threadIdx.x] = input[idx];
    int length = blockIdx.x+1 == gridDim.x ? (N+threadsPerBlock - blockDim.x*gridDim.x) : threadsPerBlock;
    __syncthreads();
    while (2*threadIdx.x + 1 < length) {
        sharedMem[threadIdx.x] += sharedMem[length-1-threadIdx.x];
        length = (length+1)/2;
        __syncthreads();
    }
    if(threadIdx.x == 0) {
        atomicAdd(output,sharedMem[0]);
    }
}

// input, output are device pointers
void solve(const float* input, float* output, int N) {  
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    sum<<<blocksPerGrid, threadsPerBlock>>>(input, output, N);
    cudaDeviceSynchronize();  
}
