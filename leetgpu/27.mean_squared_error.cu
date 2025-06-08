// URL: https://leetgpu.com/challenges/mean-squared-error
// GPU: NVIDIA TESLA T4
// Runtime: 2.82445 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void mean_square_error(const float* predictions, const float* targets, float* mse, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        const auto diff = predictions[idx] - targets[idx];
        sharedMem[threadIdx.x] = diff*diff;
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
        atomicAdd(mse,sharedMem[0]);
    }
}

__global__ void div_kernel(float* a, int b) {
    *a /= b;
}

// predictions, targets, mse are device pointers
void solve(const float* predictions, const float* targets, float* mse, int N) {
    const int threadsPerBlock = 64;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    mean_square_error<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(predictions, targets, mse, N);
    div_kernel<<<1,1>>>(mse, N);
    cudaDeviceSynchronize();  
}

