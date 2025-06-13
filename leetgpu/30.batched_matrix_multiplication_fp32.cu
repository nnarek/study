// URL: https://leetgpu.com/challenges/batched-matrix-multiplication-fp32
// GPU: NVIDIA TESLA T4
// Runtime: 2.74412 ms
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
void matrix_multiplication(const float* A, const float* B, float* C, int M, int N, int K, cudaStream_t stream) {
    dim3 threadsPerBlock(16, 16);
    dim3 blocksPerGrid((K + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    matrix_multiplication_kernel<<<blocksPerGrid, threadsPerBlock, 0, stream>>>(A, B, C, M, N, K);
}


// A, B, C are device pointers
void solve(const float* A, const float* B, float* C, int BATCH, int M, int N, int K) {

    const int max_num_streams = 32;
    cudaStream_t streams[max_num_streams];
    const int num_streams = min(max_num_streams,BATCH);
    
    for (int i = 0; i < num_streams; ++i) {
        cudaStreamCreate(&streams[i]);
    }

    for (int batch_index = 0; batch_index < BATCH; ++batch_index) {
        const float* A_ptr = A + M * K * batch_index;
        const float* B_ptr = B + K * N * batch_index;
        float* C_ptr = C + M * N * batch_index;
        matrix_multiplication(A_ptr, B_ptr, C_ptr, M, K, N, streams[batch_index%num_streams]);
    }
    cudaDeviceSynchronize();//waiting to all streams
    
    for (int i = 0; i < num_streams; ++i) {
        cudaStreamDestroy(streams[i]);
    }
}
    
