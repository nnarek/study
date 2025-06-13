// URL: https://leetgpu.com/challenges/softmax
// GPU: NVIDIA TESLA T4
// Runtime: 1.91665 ms
#include "solve.h"
#include <cuda_runtime.h>

// note that input can contain value 1000 or more, so we can not calculate its exponent 

__device__ float atomicMaxFloat(float* addr, float value) {
    int* address_as_int = (int*)addr;
    int old = *address_as_int, assumed;

    do {
        assumed = old;
        float assumed_float = __int_as_float(assumed);
        if (assumed_float >= value) break;
        old = atomicCAS(address_as_int, assumed, __float_as_int(value));
    } while (assumed != old);

    return __int_as_float(old);
}

__forceinline__ __device__ float max2(const float& a, const float& b) {
    // computing max of two float branchless 
    int32_t b_is_max = a < b;
    b_is_max = -b_is_max; // now, a_is_max contain only 0s or only 1s
    const int32_t a_is_max = ~b_is_max;

    const int32_t ia = *(int32_t*)&a;
    const int32_t ib = *(int32_t*)&b;

    const int32_t result_bits = (ia & a_is_max) | (ib & b_is_max);
    
    return *(float*)&result_bits;
}

__global__ void max_kernel(const float* input, float* max, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        sharedMem[threadIdx.x] = input[idx];
    } else {
        sharedMem[threadIdx.x] = 0.0;
    }
    __syncthreads();
    int shift_tid = threadIdx.x + 1;
    for (int shift = 1; shift < blockDim.x; shift <<= 1) {
        if(shift_tid < blockDim.x) {
            sharedMem[shift_tid - shift] = max2(sharedMem[shift_tid - shift], sharedMem[shift_tid]);
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.x == 0) {
        atomicMaxFloat(max,sharedMem[0]);
    }
}

__global__ void expf_and_sum(const float* input, float* output, float* sum, const float max, int N) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        const float exp_result = expf(input[idx]-max);
        output[idx] = exp_result;
        sharedMem[threadIdx.x] = exp_result;
    } else {
        sharedMem[threadIdx.x] = 0.0;
    }
    __syncthreads();
    int shift_tid = threadIdx.x + 1;
    for (int shift = 1; shift < blockDim.x; shift <<= 1) {
        if(shift_tid < blockDim.x) {
            sharedMem[shift_tid - shift] += sharedMem[shift_tid];
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.x == 0) {
        atomicAdd(sum,sharedMem[0]);
    }
}

__global__ void devide_kernel(float* output, float sum, int N) {
    int idx = blockIdx.x*blockDim.x + threadIdx.x;
    if(idx < N) {
        output[idx] /= sum;
    }
}

// input, output are device pointers (i.e. pointers to memory on the GPU)
void solve(const float* input, float* output, int N) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;

    float *d_max;
    cudaMallocAsync((void **)&d_max, sizeof(float), 0);
    float h_max = -INFINITY;    
    cudaMemcpyAsync(d_max, &h_max, sizeof(float), cudaMemcpyHostToDevice);
    max_kernel<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(input, d_max, N);
    cudaMemcpyAsync(&h_max, d_max, sizeof(float), cudaMemcpyDeviceToHost);
    cudaFreeAsync(d_max, 0);


    float *d_sum;
    cudaMallocAsync((void **)&d_sum, sizeof(float), 0);
    float h_sum = 0.0f;    
    cudaMemcpyAsync(d_sum, &h_sum, sizeof(float), cudaMemcpyHostToDevice);
    expf_and_sum<<<blocksPerGrid, threadsPerBlock, threadsPerBlock*sizeof(float)>>>(input, output, d_sum, h_max, N);
    cudaMemcpyAsync(&h_sum, d_sum, sizeof(float), cudaMemcpyDeviceToHost);
    cudaFreeAsync(d_sum, 0);


    devide_kernel<<<blocksPerGrid, threadsPerBlock>>>(output, h_sum, N);
    cudaDeviceSynchronize();
}
