// URL: https://leetgpu.com/challenges/color-inversion
// GPU: NVIDIA TESLA T4
// Runtime: 0.68684 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void invert_kernel(unsigned char* image, int width, int height) {
    int pixel_index = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(pixel_index < width * height)
    {
        unsigned int* point = (unsigned int*)(image+4*pixel_index);//assuming that image is 4 byte aligned
        *point = __vabsdiffu4(0x00FFFFFF,*point); //this simd instruction calculates abs difference for each byte
    }
}
// image_input, image_output are device pointers (i.e. pointers to memory on the GPU)
void solve(unsigned char* image, int width, int height) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (width * height + threadsPerBlock - 1) / threadsPerBlock;

    invert_kernel<<<blocksPerGrid, threadsPerBlock>>>(image, width, height);
    cudaDeviceSynchronize();
}
