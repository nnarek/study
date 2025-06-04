// URL: https://leetgpu.com/challenges/matrix-transpose
// GPU: NVIDIA TESLA T4
// Runtime: 2.67688 ms
#include "solve.h"
#include <cuda_runtime.h>

int BLOCK_SIZE = 16;

// following matrix are stored in row major format as [1.0 2.0 3.0 4.0 5.0 6.0] continues array
// [1.0 2.0 3.0]
// [4.0 5.0 6.0]

// in general we can say that output[x,y]==input[y,x] if all indexes are within bounds

__global__ void matrix_transpose_kernel(const float* input, float* output, int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int idy = blockIdx.y * blockDim.y + threadIdx.y;
    if(idx < cols && idy < rows) {
        output[rows*idx+idy] = input[cols*idy+idx];
    }
}

// input, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, float* output, int rows, int cols) {
    dim3 threadsPerBlock(BLOCK_SIZE, BLOCK_SIZE);
    dim3 blocksPerGrid((cols + BLOCK_SIZE - 1) / BLOCK_SIZE,
                       (rows + BLOCK_SIZE - 1) / BLOCK_SIZE);

    matrix_transpose_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, output, rows, cols);
    cudaDeviceSynchronize();
}
