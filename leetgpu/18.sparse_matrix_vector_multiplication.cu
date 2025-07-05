// URL: https://leetgpu.com/challenges/sparse-matrix-vector-multiplication
// GPU: NVIDIA TESLA T4
// Runtime: 1.82754 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void matvec_kernel(const float* A, const float* x, float* y, int M, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            sum += A[idx*N+index]*x[index];
        }
        y[idx] = sum;
    }
}

void solve(const float* A, const float* x, float* y, int M, int N, int nnz) {
    dim3 threadsPerBlock(256);
    dim3 blocksPerGrid((M + threadsPerBlock.x - 1) / threadsPerBlock.x);
    
    matvec_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, x, y, M, N);
    cudaDeviceSynchronize();
} 
