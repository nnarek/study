// URL: https://leetgpu.com/challenges/batched-matrix-multiplication-fp32
// GPU: NVIDIA TESLA T4
// Runtime: 2.75808 ms
#include "solve.h"
#include <cuda_runtime.h>

// from https://leetgpu.com/challenges/matrix-multiplication
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
void matrix_multiplication(const float* A, const float* B, float* C, int M, int N, int K) {
    dim3 threadsPerBlock(16, 16);
    dim3 blocksPerGrid((K + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    matrix_multiplication_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, M, N, K);
}


// A, B, C are device pointers
void solve(const float* A, const float* B, float* C, int BATCH, int M, int N, int K) {
    for (int batch_index = 0; batch_index < BATCH; ++batch_index) {
        matrix_multiplication(A+M*K*batch_index, B+K*N*batch_index, C+M*N*batch_index, M, K, N);
    }
    cudaDeviceSynchronize();
}
    
