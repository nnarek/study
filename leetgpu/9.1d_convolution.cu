// URL: https://leetgpu.com/challenges/1d-convolution
// GPU: NVIDIA TESLA T4
// Runtime: 5.44803 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void convolution_1d_kernel(const float* input, const float* kernel, float* output,
                                      int input_size, int kernel_size) {
    __shared__ float kernel_shared[2048];
    __shared__ float input_shared[3072];

    
    const int output_size = input_size - kernel_size + 1;
    const int idx = (blockIdx.x * blockDim.x) + threadIdx.x;

    if (threadIdx.x < kernel_size) {
        kernel_shared[threadIdx.x] = kernel[threadIdx.x];
    }
    if ((blockDim.x + threadIdx.x) < kernel_size) {
        kernel_shared[blockDim.x + threadIdx.x] = kernel[blockDim.x + threadIdx.x];
    }
    // each block access to 'input' starting from index blockIdx.x*blockDim.x to index blockIdx.x*blockDim.x+blockDim.x-1+kernel_size-1  
    // note that end index can not exceed input_size 
    // so maximum size of input_shared can be blockDim.x+kernel_size-1
    // I assume that kernel_size <= 2*blockDim.x and 3 operations are sufficient to copy the part of input which is used by current block
    if (idx < input_size) {
        input_shared[threadIdx.x] = input[idx];
    }
    if((blockDim.x+idx) < input_size && threadIdx.x < kernel_size) {//this mean that we copied blockDim.x elements in previoud operation
        input_shared[blockDim.x+threadIdx.x] = input[blockDim.x+idx];
    }
    if((2*blockDim.x+idx) < input_size && (blockDim.x+threadIdx.x) < kernel_size) {
        input_shared[2*blockDim.x+threadIdx.x] = input[2*blockDim.x+idx];
    }

    __syncthreads();

    if(idx < output_size) {
        float out = 0.0;
        for(int kernel_index = 0; kernel_index < kernel_size; ++kernel_index) {
            out += kernel_shared[kernel_index]*input_shared[threadIdx.x+kernel_index];
        }
        output[idx] = out;
    }
}

// input, kernel, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, const float* kernel, float* output, int input_size, int kernel_size) {
    int output_size = input_size - kernel_size + 1;
    int threadsPerBlock = 1024;
    int blocksPerGrid = (output_size + threadsPerBlock - 1) / threadsPerBlock;

    convolution_1d_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, kernel, output, input_size, kernel_size);
    cudaDeviceSynchronize();
}
