// URL: https://leetgpu.com/challenges/3d-convolution
// GPU: NVIDIA TESLA T4
// Runtime: 16.53112 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void convolution_3d_kernel(const float* input, const float* kernel, float* output,
                                      int input_depth, int input_rows, int input_cols,
                                      int kernel_depth, int kernel_rows, int kernel_cols) {
    __shared__ float shared_kernel[128];

    const int output_depth = input_depth - kernel_depth + 1;
    const int output_rows = input_rows - kernel_rows + 1;
    const int output_cols = input_cols - kernel_cols + 1;

    const int idx = blockIdx.x * blockDim.x + threadIdx.x;
    const int idy = blockIdx.y * blockDim.y + threadIdx.y;
    const int idz = blockIdx.z * blockDim.z + threadIdx.z;

    if(threadIdx.x < kernel_depth && threadIdx.y < kernel_rows && threadIdx.z < kernel_cols) {
        shared_kernel[threadIdx.x*kernel_rows*kernel_cols + 
                      threadIdx.y*kernel_cols + 
                      threadIdx.z] = kernel[threadIdx.x*kernel_rows*kernel_cols + 
                                            threadIdx.y*kernel_cols + 
                                            threadIdx.z];
    }

    __syncthreads();

    if(idx < output_depth && idy < output_rows && idz < output_cols) {
        float out = 0.0;
        for(int kidx = 0; kidx < kernel_depth; ++kidx) {
            for(int kidy = 0; kidy < kernel_rows; ++kidy) {
                for(int kidz = 0; kidz < kernel_cols; ++kidz) {
                    out += shared_kernel[kidx*kernel_rows*kernel_cols + 
                                         kidy*kernel_cols +
                                         kidz ] * input[(idx+kidx)*input_cols*input_rows+(idy+kidy)*input_cols+idz+kidz];
                }
            }
        }
        output[idx*output_cols*output_rows + idy*output_cols + idz] = out;
    }
}

// input, kernel, output are device pointers
void solve(const float* input, const float* kernel, float* output,
           int input_depth, int input_rows, int input_cols,
           int kernel_depth, int kernel_rows, int kernel_cols) {
    dim3 threadsPerBlock(8, 8, 8);
    const int output_depth = input_depth - kernel_depth + 1;
    const int output_rows = input_rows - kernel_rows + 1;
    const int output_cols = input_cols - kernel_cols + 1;
    dim3 blocksPerGrid((output_depth + threadsPerBlock.x - 1) / threadsPerBlock.x,
                       (output_rows + threadsPerBlock.y - 1) / threadsPerBlock.y,
                       (output_cols + threadsPerBlock.z - 1) / threadsPerBlock.z);

    convolution_3d_kernel<<<blocksPerGrid, threadsPerBlock>>>(input,kernel,output,
                                                              input_depth,input_rows,input_cols,
                                                              kernel_depth,kernel_rows,kernel_cols);
    cudaDeviceSynchronize();
}
