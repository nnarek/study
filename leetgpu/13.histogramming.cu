// URL: https://leetgpu.com/challenges/histogramming
// GPU: NVIDIA TESLA T4
// Runtime: 0.92512 ms
#include "solve.h"
#include <cuda_runtime.h>

constexpr int threadsPerBlock = 256;
constexpr int numIter = 1024/threadsPerBlock;

__global__ void histogram_kernel(const int* input, int* histogram, int N, int num_bins) {
    __shared__ int shm_hist[1024];
    
    int idx = (blockIdx.x * numIter*threadsPerBlock) + threadIdx.x;

    #pragma unroll
    for(int i = 0; i < numIter; ++i) {
        shm_hist[i*threadsPerBlock+threadIdx.x] = 0;
    }

    __syncthreads();
    #pragma unroll
    for(int i = 0; i < numIter; ++i) {
        if((i*threadsPerBlock+idx) < N) {
            atomicAdd(shm_hist + input[i*threadsPerBlock+idx], 1);
        }
    }
    __syncthreads();
    #pragma unroll
    for(int i = 0; i < numIter; ++i) {
        if((i*threadsPerBlock+threadIdx.x) < num_bins) {
            atomicAdd(histogram + i*threadsPerBlock+threadIdx.x, shm_hist[i*threadsPerBlock+threadIdx.x]);
        } 
    }
}

void solve(const int* input, int* histogram, int N, int num_bins) {
    int blocksPerGrid = (N + numIter * threadsPerBlock - 1) / (numIter * threadsPerBlock);
    histogram_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, histogram, N, num_bins);
    cudaDeviceSynchronize();
}
