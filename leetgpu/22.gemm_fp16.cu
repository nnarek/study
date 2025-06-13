// URL: https://leetgpu.com/challenges/gemm-fp16
// GPU: NVIDIA TESLA T4
// Runtime: 4.36598 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <cuda_fp16.h>

// simple solution which have bank conflicts
__global__ void gemm_kernel(const half* A, const half* B, half* C, int M, int N, int K, float alpha, float beta) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < N && idy < M) {
        float sum_ab = 0.0;
        for(int index = 0; index < K; ++index) {
            sum_ab += __half2float(A[idy*K+index])*__half2float(B[index*N+idx]);
        }
        const int index = idy*N+idx;
        C[index] = __float2half(sum_ab*alpha + __half2float(C[index])*beta);
    }
}

// A, B, and C are device pointers
void solve(const half* A, const half* B, half* C, int M, int N, int K, float alpha, float beta) {
    dim3 threadsPerBlock(16, 16);
    dim3 blocksPerGrid((N + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    gemm_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, M, N, K, alpha, beta);
    cudaDeviceSynchronize();
}

