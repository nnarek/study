// URL: https://leetgpu.com/challenges/quantized-matrix-multiplication-int8
// GPU: NVIDIA TESLA T4
// Runtime: 259.72737 ms
#include "solve.h"
#include <cuda_runtime.h>

__device__ long clamp(long x, long a, long b) {
    if(x < a) {
        return a;
    } else if(b < x) {
        return b;
    } else {
        return x;
    }
}

__global__ void quantized_matmul_kernel(const int8_t* A, const int8_t* B, int8_t* C, 
                                        int M, int N, int K, 
                                        float scale_A, float scale_B, float scale_C, 
                                        int zero_point_A, int zero_point_B, int zero_point_C) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < N && idy < M) {
        int sum = 0.0;
        for(int index = 0; index < K; ++index) {
            sum += (A[idy*K+index]-zero_point_A)*(B[index*N+idx]-zero_point_B);
        }
        C[idy*N+idx] = clamp(lroundf(sum*scale_B*scale_A/scale_C)+zero_point_C,-128,127);
    }
}

void solve(const int8_t* A, const int8_t* B, int8_t* C, 
           int M, int N, int K, 
           float scale_A, float scale_B, float scale_C, 
           int zero_point_A, int zero_point_B, int zero_point_C) {
    dim3 threadsPerBlock(16, 16);
    dim3 blocksPerGrid((N + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    quantized_matmul_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, M, N, K, 
           scale_A, scale_B, scale_C, zero_point_A, zero_point_B, zero_point_C);
    cudaDeviceSynchronize();
} 
