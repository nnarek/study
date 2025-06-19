// URL: https://leetgpu.com/challenges/softmax-attention
// GPU: NVIDIA TESLA T4
// Runtime: 1.24235 ms
#include "solve.h"
#include <cuda_runtime.h>

// space complexity of current solution is M*N which can be 10^10 according to constraints of this challenge

// from https://leetgpu.com/challenges/matrix-multiplication
__global__ void matmul_kernel(const float* A, const float* B, float* C, int M, int N, int K) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < K && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            sum += A[idy*N+index]*B[index*K+idx];
        }
        C[idy*K+idx] = sum;
    }
}

// modified https://leetgpu.com/challenges/matrix-multiplication
__global__ void matmul_transposed_kernel(const float* A, const float* B, float* C, int M, int N, int K) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < K && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            sum += A[idy*N+index]*B[idx*N+index];
        }
        C[idy*K+idx] = sum;
    }
}

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

__global__ void max_kernel(const float* input, float* row_max, int rows, int cols) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idy < cols) {
        sharedMem[threadIdx.y] = input[idx*cols+idy];
    } else {
        sharedMem[threadIdx.y] = 0.0;
    }
    __syncthreads();
    int shift_tid = threadIdx.y + 1;
    for (int shift = 1; shift < blockDim.y; shift <<= 1) {
        if(shift_tid < blockDim.y) {
            sharedMem[shift_tid - shift] = fmaxf(sharedMem[shift_tid - shift], sharedMem[shift_tid]);
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.y == 0) {
        atomicMaxFloat(row_max + idx,sharedMem[0]);
    }
}

__global__ void expf_and_sum(float* input, float* sum, const float* max, int rows, int cols, float sqrt_d) {
    extern __shared__ float sharedMem[];

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idy < cols) {
        const float exp_result = expf((input[idx*cols+idy]-max[idx])/sqrt_d);
        input[idx*cols+idy] = exp_result;
        sharedMem[threadIdx.y] = exp_result;
    } else {
        sharedMem[threadIdx.y] = 0.0;
    }
    __syncthreads();
    int shift_tid = threadIdx.y + 1;
    for (int shift = 1; shift < blockDim.y; shift <<= 1) {
        if(shift_tid < blockDim.y) {
            sharedMem[shift_tid - shift] += sharedMem[shift_tid];
        } 
        __syncthreads();
        shift_tid <<= 1;
    }
    if(threadIdx.y == 0) {
        atomicAdd(sum+idx,sharedMem[0]);
    }
}

__global__ void divide_kernel(float* input, const float* sum, int rows, int cols) {
    __shared__ float sum_shared;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(threadIdx.y == 0){
        sum_shared = sum[idx];
    }
    __syncthreads();
    if(idy < cols) {
        input[idx*cols+idy] /= sum_shared;
    }
}

__global__ void fill_kernel(float* input, float val, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        input[idx] = val;
    }
}

// Q, K, V, output are device pointers
void solve(const float* Q, const float* K, const float* V, float* output, int M, int N, int d) {
    float *QKT;
    {
        dim3 threadsPerBlock(16, 16);
        dim3 blocksPerGrid((N + threadsPerBlock.x - 1) / threadsPerBlock.x,
                        (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
        cudaMallocAsync((void **)&QKT, M*N*sizeof(float), 0);
        cudaMemsetAsync(QKT, 0, M*N*sizeof(float), 0);
        matmul_transposed_kernel<<<blocksPerGrid, threadsPerBlock>>>(Q, K, QKT, M, d, N);
    }

    float *row_max;
    {
        cudaMallocAsync((void **)&row_max, M*sizeof(float), 0);
        int threadsPerBlock = 256;
        int blocksPerGrid = (M + threadsPerBlock - 1)/threadsPerBlock;
        fill_kernel<<<blocksPerGrid,threadsPerBlock>>>(row_max,-INFINITY,M);
    }
    {
        dim3 threadsPerBlock(1,256);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y);
        max_kernel<<<blocksPerGrid,threadsPerBlock,threadsPerBlock.y*sizeof(float)>>>(QKT,row_max,M,N);
    }

    float *row_sum;
    {
        cudaMallocAsync((void **)&row_sum, M*sizeof(float), 0);
        cudaMemsetAsync(row_sum, 0, M*sizeof(float), 0);
        dim3 threadsPerBlock(1,256);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y);
        expf_and_sum<<<blocksPerGrid, threadsPerBlock, threadsPerBlock.y*sizeof(float)>>>(QKT, row_sum, row_max,M,N,sqrt(d));
    }

    {
        dim3 threadsPerBlock(1,256);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y);
        divide_kernel<<<blocksPerGrid, threadsPerBlock>>>(QKT, row_sum,M,N);
    }

    cudaFreeAsync(row_max, 0);
    cudaFreeAsync(row_sum, 0);

    {
        dim3 threadsPerBlock(16, 16);
        dim3 blocksPerGrid((d + threadsPerBlock.x - 1) / threadsPerBlock.x,
                        (M + threadsPerBlock.y - 1) / threadsPerBlock.y);
        matmul_kernel<<<blocksPerGrid, threadsPerBlock>>>(QKT, V, output, M, N, d);
    }

    cudaFreeAsync(QKT, 0);
    cudaDeviceSynchronize();
}

