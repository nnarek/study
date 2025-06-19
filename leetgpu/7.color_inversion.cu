// URL: https://leetgpu.com/challenges/color-inversion
// GPU: NVIDIA TESLA T4
// Runtime: 0.68709 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void invert_kernel(unsigned char* image, int width, int height) {
    int pixel_index = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(pixel_index < width * height)
    {
        unsigned int* point = (unsigned int*)(image+4*pixel_index);
        const auto point_masked = *point | 0x00FFFFFF; //preserving last char and asigning 255 to others 
        const auto point_without_last = *point & 0x00FFFFFF; //assigning 0 to last char and preserving others
        *point = point_masked - point_without_last; //will not cause overflow for non of chars because of constraints of this challenge
    }
}
// image_input, image_output are device pointers (i.e. pointers to memory on the GPU)
void solve(unsigned char* image, int width, int height) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (width * height + threadsPerBlock - 1) / threadsPerBlock;

    invert_kernel<<<blocksPerGrid, threadsPerBlock>>>(image, width, height);
    cudaDeviceSynchronize();
}
