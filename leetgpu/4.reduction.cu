// URL: https://leetgpu.com/challenges/reduction
// GPU: NVIDIA TESLA T4
// Runtime: 2.39442 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <iostream>

const int threadsPerBlock = 1024;

__global__ void sum(const float* input, float* output, int N) {
    __shared__ float sharedMem[threadsPerBlock];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx >= N) {
        return;
    }
    sharedMem[threadIdx.x] = input[idx];
    int length = blockIdx.x+1 == gridDim.x ? (N+threadsPerBlock - blockDim.x*gridDim.x) : threadsPerBlock;
    __syncthreads();
    while (2*threadIdx.x + 1 < length) {
        sharedMem[threadIdx.x] += sharedMem[length-1-threadIdx.x];
        length = (length+1)/2;
        __syncthreads();
    }
    if(threadIdx.x == 0) {
        output[blockIdx.x] = sharedMem[0];
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
