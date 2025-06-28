// URL: https://leetgpu.com/challenges/monte-carlo-integration
// GPU: NVIDIA TESLA T4
// Runtime: 0.08707 ms
#include "solve.h"
#include <cuda_runtime.h>

#include "solve.h"
#include <cuda_runtime.h>


__global__ void sum(const float* input, float* output, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        sharedMem[threadIdx.x] = input[idx];
    } else {
        sharedMem[threadIdx.x] = 0.0;
    }
    __syncthreads();
    //approach is to add each shift-rd element
    int shift_tid = threadIdx.x + 1;
    for (int shift = 1; shift < blockDim.x; shift <<= 1) {//all threads should have same amount iterations to avoid from conditional __syncthreads
        if(shift_tid < blockDim.x) {
            sharedMem[shift_tid - shift] += sharedMem[shift_tid];
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.x == 0) {
        atomicAdd(output,sharedMem[0]);
    }
}

__global__ void normalize_kernel(float* sum,float a, float b, int n_samples) {
    *sum /= n_samples;
    *sum *= (b - a);
}


// y_samples, result are device pointers
void solve(const float* y_samples, float* result, float a, float b, int n_samples) {
    const int threadsPerBlock = 64;
    int blocksPerGrid = (n_samples + threadsPerBlock - 1) / threadsPerBlock;
    sum<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(y_samples,result,n_samples);
    normalize_kernel<<<1,1>>>(result,a,b,n_samples);
    cudaDeviceSynchronize();  
}

