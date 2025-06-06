// URL: https://leetgpu.com/challenges/gaussian-blur
// GPU: NVIDIA TESLA T4
// Runtime: 0.92288 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void gaussian_blur(const float* input, const float* kernel, float* output,
                             int input_rows, int input_cols, int kernel_rows, int kernel_cols) {
    __shared__ float shared_kernel[512];

    const int idx = blockIdx.x * blockDim.x + threadIdx.x;
    const int idy = blockIdx.y * blockDim.y + threadIdx.y;

    const int kernel_center_x = kernel_rows/2;
    const int kernel_center_y = kernel_cols/2;

    if(threadIdx.x < kernel_rows && threadIdx.y < kernel_cols) {
        shared_kernel[threadIdx.x*kernel_cols + threadIdx.y] = kernel[threadIdx.x*kernel_cols + threadIdx.y];
    }

    __syncthreads();

    if(idx < input_rows && idy < input_cols) {
        float out = 0.0;
        for(int kidx = -kernel_center_x; kidx <= kernel_center_x; ++kidx) {
            for(int kidy = -kernel_center_y; kidy <= kernel_center_y; ++kidy) {
                if(0 <= idx+kidx && idx+kidx < input_rows && 0 <= idy+kidy && idy+kidy < input_cols) {
                    out += shared_kernel[(kernel_center_x+kidx)*kernel_cols + kidy+kernel_center_y]*input[(idx+kidx)*input_cols+idy+kidy];
                }
            }
        }
        output[idx*input_cols + idy] = out;
    }
}

// input, kernel, output are device pointers
void solve(const float* input, const float* kernel, float* output,
           int input_rows, int input_cols, int kernel_rows, int kernel_cols) {
    dim3 threadsPerBlock(32, 32);
    dim3 blocksPerGrid((input_cols + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (input_rows + threadsPerBlock.y - 1) / threadsPerBlock.y);
    
    gaussian_blur<<<blocksPerGrid, threadsPerBlock>>>(input,kernel,output,input_rows,
                                                      input_cols,kernel_rows,kernel_cols);
    cudaDeviceSynchronize();
}

