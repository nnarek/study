// URL: https://leetgpu.com/challenges/reverse-array
// GPU: NVIDIA TESLA T4
// Runtime: 0.82601 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void reverse_array(float* input, int N) {
    int global_index = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(2*global_index < N)
    {
        const auto temp = input[N-1-global_index];
        input[N-1-global_index] = input[global_index];
        input[global_index] = temp;
    }
}

// input is device pointer
void solve(float* input, int N) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N/2 + threadsPerBlock - 1) / threadsPerBlock;

    reverse_array<<<blocksPerGrid, threadsPerBlock>>>(input, N);
    cudaDeviceSynchronize();
}
