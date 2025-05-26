// URL: https://leetgpu.com/challenges/vector-addition
// GPU: NVIDIA TESLA T4
// Runtime: 1.15245 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void vector_add(const float* A, const float* B, float* C, int N) {
    int globalId = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(globalId < N) {
        C[globalId] = A[globalId] + B[globalId];
    }
}

// A, B, C are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* A, const float* B, float* C, int N) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;

    vector_add<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, N);
    cudaDeviceSynchronize();
}

