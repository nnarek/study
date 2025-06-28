// URL: https://leetgpu.com/challenges/gaussian-blur
// GPU: NVIDIA TESLA T4
// Runtime: 0.16197 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void gaussian_blur(const float* input, const float* kernel, float* output,
                             int input_rows, int input_cols, int kernel_rows, int kernel_cols) {
    __shared__ float shared_kernel[512]; // 21*21 < 512
    __shared__ float shared_input[3072]; //(21+32)*(21+32) < 3072

    const int idx = blockIdx.x * blockDim.x + threadIdx.x;
    const int idy = blockIdx.y * blockDim.y + threadIdx.y;

    const int kernel_center_x = kernel_rows/2;
    const int kernel_center_y = kernel_cols/2;

    const int shared_input_rows = blockDim.x + kernel_rows;
    const int shared_input_cols = blockDim.y + kernel_cols;

    if(threadIdx.x < kernel_rows && threadIdx.y < kernel_cols) {
        shared_kernel[threadIdx.x*kernel_cols + threadIdx.y] = kernel[threadIdx.x*kernel_cols + threadIdx.y];
    }
    // we need to copy elements from blockIdx.x*blockDim.x-kernel_center_x to blockIdx.x*blockDim.x+blockDim.x+kernel_center_x
    if (0 <= (idx-kernel_center_x) && (idx-kernel_center_x) < input_rows) {
        if (0 <= (idy-kernel_center_y) && (idy-kernel_center_y) < input_cols) {
            shared_input[threadIdx.x*shared_input_cols+threadIdx.y] 
                = input[(idx-kernel_center_x)*input_cols+(idy-kernel_center_y)];
        }
        if(0 <= (blockDim.y+idy-kernel_center_y) && (blockDim.y+idy-kernel_center_y) < input_cols && threadIdx.y < kernel_cols) {
            shared_input[threadIdx.x*shared_input_cols+blockDim.y+threadIdx.y] 
                = input[(idx-kernel_center_x)*input_cols+blockDim.y+(idy-kernel_center_y)];
        }
    }
    if (0 <= (blockDim.x+idx-kernel_center_x) && (idx-kernel_center_x) < input_rows && threadIdx.x < kernel_rows) {
        if (0 <= (idy-kernel_center_y) && (idy-kernel_center_y) < input_cols) {
            shared_input[(blockDim.x+threadIdx.x)*shared_input_cols+threadIdx.y] 
                = input[(blockDim.x+idx-kernel_center_x)*input_cols+(idy-kernel_center_y)];
        }
        if(0 <= (blockDim.y+idy-kernel_center_y) && (blockDim.y+idy-kernel_center_y) < input_cols && threadIdx.y < kernel_cols) {
            shared_input[(blockDim.x+threadIdx.x)*shared_input_cols+blockDim.y+threadIdx.y] 
                = input[(blockDim.x+idx-kernel_center_x)*input_cols+blockDim.y+(idy-kernel_center_y)];
        }
    }

    __syncthreads();

    if(idx < input_rows && idy < input_cols) {
        float out = 0.0;
        for(int kidx = -kernel_center_x; kidx <= kernel_center_x; ++kidx) {
            for(int kidy = -kernel_center_y; kidy <= kernel_center_y; ++kidy) {
                if(0 <= idx+kidx && idx+kidx < input_rows && 0 <= idy+kidy && idy+kidy < input_cols) {
                    out += shared_kernel[(kernel_center_x+kidx)*kernel_cols + kidy+kernel_center_y]
                           * shared_input[(threadIdx.x+kidx+kernel_center_x)*shared_input_cols+threadIdx.y+kidy+kernel_center_y];
                           // coordinates of shared_input are shifted by kernel_center_x and kernel_center_y
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

