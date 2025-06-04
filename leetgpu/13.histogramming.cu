// URL: https://leetgpu.com/challenges/histogramming
// GPU: NVIDIA TESLA T4
// Runtime: 1.30856 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void histogram_kernel(const int* input, int* histogram, int N, int num_bins) {
    extern __shared__ int shm_hist[];
    
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        if(threadIdx.x < num_bins) {
            shm_hist[threadIdx.x] = 0;
        }
        __syncthreads();
        atomicAdd(shm_hist + input[idx],1);
        __syncthreads();
        if(threadIdx.x < num_bins) {
            atomicAdd(histogram + threadIdx.x,shm_hist[threadIdx.x]);
        }
    }
}

// input, histogram are device pointers
void solve(const int* input, int* histogram, int N, int num_bins) {
    const int threadsPerBlock = 1024;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    histogram_kernel<<<blocksPerGrid, threadsPerBlock, num_bins*sizeof(int)>>>(input, histogram, N, num_bins);
    cudaDeviceSynchronize();
}
