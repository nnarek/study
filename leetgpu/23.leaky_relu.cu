// URL: https://leetgpu.com/challenges/leaky-relu
// GPU: NVIDIA TESLA T4
// Runtime: 1.65672 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void leaky_relu_kernel(const float* input, float* output, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        const float val = input[idx];
        // branchless sign check function
        // if we want to calculate output by val*coef then coef should be 1 if val is positive and 0.01 if val is negative
        // we can use copysignf(x,val)=x*sign_of_val function to calculate coef
        // let use simplist calulations which we can do, for example coef=copysignf(x,val)+y
        // for positive vals we have 1=x+y
        // for negative val we have 0.01=-x+y
        // solving this we will get below code
        const float coef = copysignf(0.495f, val)+0.505f;
        output[idx] = val*coef;
    }
}

// input, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, float* output, int N) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    
    leaky_relu_kernel<<<blocksPerGrid, threadsPerBlock>>>(input, output, N);
    cudaDeviceSynchronize();
}
