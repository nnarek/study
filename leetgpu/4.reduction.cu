// URL: https://leetgpu.com/challenges/reduction
// GPU: NVIDIA TESLA T4
// Runtime: 1.74755 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <iostream>

constexpr int threadsPerBlock = 1024;
#define FULL_MASK 0xffffffff

__global__ void sum(const float* input, float* output, int N) {
    constexpr int warpSize = 32;
    constexpr int numWarpsPerBlock = threadsPerBlock/warpSize;
    __shared__ float warp_sums[numWarpsPerBlock]; // sum reduction output of each warp

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int warpIdx = threadIdx.x/warpSize;

    float val;
    if(idx < N) {
        val = input[idx];
    } else {
        val = 0.0f;
    }
    __syncwarp();
    #pragma unroll
    for (int offset = warpSize/2; offset > 0; offset /= 2) {
        val += __shfl_down_sync(FULL_MASK, val, offset);
    }
    if((threadIdx.x%warpSize) == 0) {//first thread of each warp
        warp_sums[warpIdx] = val;
    }
    __syncthreads();

    if(warpIdx == 0) { // first warp of current block
        val = warp_sums[threadIdx.x];
        __syncwarp();
        #pragma unroll
        for (int offset = numWarpsPerBlock/2; offset > 0; offset /= 2) {
            val += __shfl_down_sync(FULL_MASK, val, offset);
        }
        if(threadIdx.x == 0) {
            output[blockIdx.x] = val;
        }
    }
}

// input, output are device pointers
void solve(const float* input, float* output, int N) {  
    if(N == 1) {
        cudaMemcpy(output, input, sizeof(float),cudaMemcpyDeviceToDevice);
        return;
    } else if(N <= threadsPerBlock) {
        sum<<<1, threadsPerBlock>>>(input, output, N);
        cudaDeviceSynchronize();
        return;
    }
    float *temp_data = NULL;

    cudaError_t err;

    const float* current_buffer = input;
    int length = N;
    
    int blocksPerGrid = (length + threadsPerBlock - 1) / threadsPerBlock;
    size_t memSize = blocksPerGrid * sizeof(float);
    err = cudaMalloc((void**)&temp_data, 2*memSize);
    if (err != cudaSuccess) {
        std::cerr << "CUDA error: " << cudaGetErrorString(err) << std::endl;
        exit(4);
    }
    float *temp_data1 = temp_data;
    float *temp_data2 = temp_data+blocksPerGrid;
    while (1 < length) {
        int blocksPerGrid = (length + threadsPerBlock - 1) / threadsPerBlock;
        sum<<<blocksPerGrid, threadsPerBlock>>>(current_buffer, temp_data1, length);
        cudaDeviceSynchronize();
        current_buffer = temp_data1;
        std::swap(temp_data1,temp_data2);        
        length = blocksPerGrid;
    }

    cudaMemcpy(output, current_buffer, sizeof(float),cudaMemcpyDeviceToDevice);

    err = cudaFree(temp_data);
    if (err != cudaSuccess) {
        std::cerr << "CUDA error: " << cudaGetErrorString(err) << std::endl;
        exit(5);
    }   
}
