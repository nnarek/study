// URL: https://leetgpu.com/challenges/reduction
// GPU: NVIDIA TESLA T4
// Runtime: 1.43057 ms
#include "solve.h"
#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include <iostream>

constexpr int threadsPerBlock = 256;

namespace cg = cooperative_groups;

__global__ void sum(const float* input, float* output, int N) {
    constexpr int warpSize = 32;
    constexpr int numWarpsPerBlock = threadsPerBlock / warpSize;
    __shared__ float warp_sums[numWarpsPerBlock];

    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    float val = (idx < N) ? input[idx] : 0.0f;

    cg::thread_block block = cg::this_thread_block(); // all threads of current block
    cg::thread_block_tile<warpSize> warp = cg::tiled_partition<warpSize>(block); // split threads of block into threadsPerBlock/warpSize thread block tiles where each one have warpSize threads
    
    #pragma unroll
    for (int offset = warpSize / 2; offset > 0; offset /= 2) {
        val += warp.shfl_down(val, offset); // same as __shfl_down, work only for thread block tiles which size is less than 32
    }

    if (warp.thread_rank() == 0) { // warp.thread_rank() == threadIdx.x % warpSize which is same as id of thread inside its thread_block_tile
        warp_sums[warp.meta_group_rank()] = val; // warp.meta_group_rank() == threadIdx.x/warpSize which is same as id of thread_block_tile inside block
    }

    block.sync(); // same as __syncthread();

    if (warp.meta_group_rank() == 0) {
        val = warp.thread_rank() < numWarpsPerBlock ? warp_sums[warp.thread_rank()] : 0.0f;
        //cg::sync(warp); // not needed here, but equivalent to __syncwarp() if number of threads in thread_block_tile is 32
        #pragma unroll
        for (int offset = numWarpsPerBlock / 2; offset > 0; offset /= 2) {
            val += warp.shfl_down(val, offset);
        }

        if (warp.thread_rank() == 0) {
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
