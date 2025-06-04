// URL: https://leetgpu.com/challenges/histogramming
// GPU: NVIDIA TESLA T4
// Runtime: 17.229 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void histogram_kernel(const int* input, int* histogram, int N, int num_bins) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        atomicAdd(histogram + input[idx],1);
    }
}

// input, histogram are device pointers
void solve(const int* input, int* histogram, int N, int num_bins) {
    const int threadsPerBlock = 1024;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    histogram_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, histogram, N, num_bins);
    cudaDeviceSynchronize();
}