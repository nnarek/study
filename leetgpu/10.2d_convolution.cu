// URL: https://leetgpu.com/challenges/2d-convolution
// GPU: NVIDIA TESLA T4
// Runtime: 68.4627 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void convolution_2d_kernel(const float* input, const float* kernel, float* output,
                                      int input_rows, int input_cols, int kernel_rows, int kernel_cols) {
    __shared__ float shared_kernel[1024];

    const int output_rows = input_rows - kernel_rows + 1;
    const int output_cols = input_cols - kernel_cols + 1;
    const int idx = blockIdx.x * blockDim.x + threadIdx.x;
    const int idy = blockIdx.y * blockDim.y + threadIdx.y;

    if(threadIdx.x < kernel_rows && threadIdx.y < kernel_cols) {
        shared_kernel[threadIdx.x*kernel_cols + threadIdx.y] = kernel[threadIdx.x*kernel_cols + threadIdx.y];
    }

    __syncthreads();

    if(idx < output_rows && idy < output_cols) {
        float out = 0.0;
        for(int kidx = 0; kidx < kernel_rows; ++kidx) {
            for(int kidy = 0; kidy < kernel_cols; ++kidy) {
                out += shared_kernel[kidx*kernel_cols + kidy]*input[(idx+kidx)*input_cols+idy+kidy];
            }
        }
        output[idx*output_cols + idy] = out;
    }
}

// input, kernel, output are device pointers
void solve(const float* input, const float* kernel, float* output,
           int input_rows, int input_cols, int kernel_rows, int kernel_cols) {
    dim3 threadsPerBlock(32, 32);
    const int output_rows = input_rows - kernel_rows + 1;
    const int output_cols = input_cols - kernel_cols + 1;
    dim3 blocksPerGrid((output_rows + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (output_cols + threadsPerBlock.y - 1) / threadsPerBlock.y);

    convolution_2d_kernel<<<blocksPerGrid, threadsPerBlock>>>(input,kernel,output,input_rows,input_cols,kernel_rows,kernel_cols);
    cudaDeviceSynchronize();
}


