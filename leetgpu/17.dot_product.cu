// URL: https://leetgpu.com/challenges/dot-product
// GPU: NVIDIA TESLA T4
// Runtime: 1.6955 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void dot_product(const float* A, const float* B, float* result, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        sharedMem[threadIdx.x] = A[idx]*B[idx];
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
        atomicAdd(result,sharedMem[0]);
    }
}

// A, B, result are device pointers
void solve(const float* A, const float* B, float* result, int N) {  
    const int threadsPerBlock = 64;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    dot_product<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(A, B, result, N);
    cudaDeviceSynchronize();  
}

