// URL: https://leetgpu.com/challenges/matrix-power
// GPU: NVIDIA TESLA T4
// Runtime: 3.01964 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void matmul_kernel(const float* A, const float* B, float* C, size_t size) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < size && col < size) {
        float sum = 0.0f;
        for (int k = 0; k < size; ++k) {
            sum += A[row * size + k] * B[k * size + col];
        }
        C[row * size + col] = sum;
    }
}

void matmul(const float* A, const float* B, float* C, size_t size) {
    dim3 threads(16, 16);
    dim3 blocks((size + threads.x-1 ) / threads.x, (size + threads.y-1) / threads.y);
    matmul_kernel<<<blocks, threads>>>(A, B, C, size);
}

// input, output are device pointers
void solve(const float* input_matrix, float* output_matrix, int size, int n) {
    float* temp;

    cudaMemcpyAsync(output_matrix, input_matrix, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
    cudaMalloc(&temp, size * size * sizeof(float));//TODO why it become way slow when I make this call async????
    
    for (size_t i = 1; i < n; ++i) {
        matmul(output_matrix, input_matrix, temp, size);

        cudaMemcpyAsync(output_matrix, temp, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
    }
    cudaDeviceSynchronize();

    cudaFree(temp);
}
