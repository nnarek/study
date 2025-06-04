// URL: https://leetgpu.com/challenges/relu-activation
// GPU: NVIDIA TESLA T4
// Runtime: 1.07525 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void relu_kernel(const float* input, float* output, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        const float val = input[idx];
        if(val <= 0) {
            output[idx] = 0;
        } else {
            output[idx] = val;
        }
    }
}

// input, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, float* output, int N) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;

    relu_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, output, N);
    cudaDeviceSynchronize();
}

