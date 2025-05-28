// URL: https://leetgpu.com/challenges/1d-convolution
// GPU: NVIDIA TESLA T4
// Runtime: 15.18912 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void convolution_1d_kernel(const float* input, const float* kernel, float* output,
                                      int input_size, int kernel_size) {
    int output_size = input_size - kernel_size + 1;
    int output_index = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(output_index < output_size) {
        for(int kernel_index = 0; kernel_index < kernel_size; ++kernel_index) {
            output[output_index] += kernel[kernel_index]*input[output_index+kernel_index];
        }
    }
}

// input, kernel, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, const float* kernel, float* output, int input_size, int kernel_size) {
    int output_size = input_size - kernel_size + 1;
    int threadsPerBlock = 256;
    int blocksPerGrid = (output_size + threadsPerBlock - 1) / threadsPerBlock;

    convolution_1d_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, kernel, output, input_size, kernel_size);
    cudaDeviceSynchronize();
}
