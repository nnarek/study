// URL: https://leetgpu.com/challenges/batched-matrix-multiplication-fp32
// GPU: NVIDIA TESLA T4
// Runtime: 1.68983 ms
#include "solve.h"
#include <cuda_runtime.h>

// we can try to reuse code of 2d multiplication
// from https://leetgpu.com/challenges/matrix-multiplication
__forceinline__  __device__ void matrix_multiplication_kernel_inline(const float* A, const float* B, float* C, int M, int N, int K) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < N && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < K; ++index) {
            sum += A[idy*K+index]*B[index*N+idx];
        }
        C[idy*N+idx] = sum;
    }
}

// unlike solution with streams, here scheduler of gpu will decide when and which parts of jobs execute(parallely or not parallely)
// we can stil reuse code of 2d matrix multiplication
__global__ void batch_matrix_multiplication_kernel(const float* A, const float* B, float* C, int BATCH, int M, int N, int K) {
    int batch_index = (blockIdx.z * blockDim.z) + threadIdx.z;
    if(batch_index < BATCH) {
        const float* A_ptr = A + M * K * batch_index;
        const float* B_ptr = B + K * N * batch_index;
        float* C_ptr = C + M * N * batch_index;
        // we also can use dynamic parallelism to run matrix_multiplication kernel from inside this batched kernel
        // but I guess it will have lower performance compared with current solution 
        matrix_multiplication_kernel_inline(A_ptr, B_ptr, C_ptr, M, N, K);
    }
}

// A, B, C are device pointers
void solve(const float* A, const float* B, float* C, int BATCH, int M, int N, int K) {
    dim3 threadsPerBlock(32, 32, 1);
    dim3 blocksPerGrid((N + threadsPerBlock.x - 1) / threadsPerBlock.x,
                        (M + threadsPerBlock.y - 1) / threadsPerBlock.y,
                        (BATCH + threadsPerBlock.z - 1) / threadsPerBlock.z);
    batch_matrix_multiplication_kernel<<<blocksPerGrid, threadsPerBlock>>>(A, B, C, BATCH, M, N, K);
}
    
