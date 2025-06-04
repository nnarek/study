// URL: https://leetgpu.com/challenges/matrix-multiplication
// GPU: NVIDIA TESLA T4
// Runtime: 934.62935 ms
#include "solve.h"
#include <cuda_runtime.h>
#include "stdio.h"

__global__ void matrix_multiplication_kernel(const float* A, const float* B, float* C, int M, int N, int K) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < K && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            sum += A[idy*N+index]*B[index*K+idx];
        }
        C[idy*K+idx] = sum;
    }
}

// A, B, C are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* A, const float* B, float* C, int M, int N, int K) {
    dim3 threadsPerBlock(16, 16);
    dim3 blocksPerGrid((K + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    matrix_multiplication_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, M, N, K);
    cudaDeviceSynchronize();
}

