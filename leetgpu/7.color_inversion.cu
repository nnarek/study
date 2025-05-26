// URL: https://leetgpu.com/challenges/color-inversion
// GPU: NVIDIA TESLA T4
// Runtime: 0.76354 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void invert_kernel(unsigned char* image, int width, int height) {
    int pixel_index = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(pixel_index < width * height)
    {
        image[4*pixel_index] = 255 - image[4*pixel_index];
        image[4*pixel_index+1] = 255 - image[4*pixel_index+1];
        image[4*pixel_index+2] = 255 - image[4*pixel_index+2];
    }
}
// image_input, image_output are device pointers (i.e. pointers to memory on the GPU)
void solve(unsigned char* image, int width, int height) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (width * height + threadsPerBlock - 1) / threadsPerBlock;

    invert_kernel<<<blocksPerGrid, threadsPerBlock>>>(image, width, height);
    cudaDeviceSynchronize();
}
