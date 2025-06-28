// URL: https://leetgpu.com/challenges/multi-head-self-attention
// GPU: NVIDIA TESLA T4
// Runtime: 28.98354 ms
#include "solve.h"
#include <cuda_runtime.h>

// refactored solution of https://leetgpu.com/challenges/softmax-attention to make it batched

__global__ void matmul_transposed_kernel(const float* A, const float* B, float* C, int M,int N,int K, int heads) {
    const int idh = (blockIdx.z * blockDim.z) + threadIdx.z;
    const int d = N;
    const int d_model = d*heads;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < K && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            //first element of idh-rd matrix placed in the idh*d
            //to jump into next row of same column we always need to jump by d_model
            sum += A[idh*d+idy*d_model+index]*B[idh*d+idx*d_model+index]; 
        }
        C[idh*M*K+idy*K+idx] = sum;//elements stored in C in format of 3D matrix
    }
}

__global__ void matmul_kernel(const float* A, const float* B, float* C, int M,int N,int K, int heads) {
    const int idh = (blockIdx.z * blockDim.z) + threadIdx.z;
    const int d = K;
    const int d_model = d*heads;


    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idx < K && idy < M) {
        float sum = 0.0;
        for(int index = 0; index < N; ++index) {
            sum += A[idh*N*M+idy*N+index]*B[idh*d+index*d_model+idx];
        }
        C[idh*d+idy*d_model+idx] = sum;
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

__global__ void max_kernel(const float* input, float* row_max, int rows, int cols, int heads) {
    extern __shared__ float sharedMem[];

    const int idh = (blockIdx.z * blockDim.z) + threadIdx.z;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idy < cols) {
        sharedMem[threadIdx.y] = input[idh*rows*cols+idx*cols+idy];
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
        atomicMaxFloat(row_max + rows*idh + idx,sharedMem[0]);
    }
}

__global__ void expf_and_sum(float* input, float* sum, const float* max, int rows, int cols, float sqrt_d, int heads) {
    extern __shared__ float sharedMem[];

    const int idh = (blockIdx.z * blockDim.z) + threadIdx.z;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(idy < cols) {
        const float exp_result = expf((input[idh*rows*cols + idx*cols+idy]-max[idh*rows + idx])/sqrt_d);
        input[idh*rows*cols + idx*cols+idy] = exp_result;
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
        atomicAdd(sum + idh*rows + idx,sharedMem[0]);
    }
}

__global__ void divide_kernel(float* input, const float* sum, int rows, int cols, int heads) {
    __shared__ float sum_shared;

    const int idh = (blockIdx.z * blockDim.z) + threadIdx.z;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(threadIdx.y == 0){
        sum_shared = sum[idh*rows + idx];
    }
    __syncthreads();
    if(idy < cols) {
        input[idh*rows*cols + idx*cols+idy] /= sum_shared;
    }
}

__global__ void fill_kernel(float* input, float val, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        input[idx] = val;
    }
}

// Q, K, V, output are device pointers
void solve(const float* Q, const float* K, const float* V, float* output, int N, int d_model, int h) {
    const int M = N;
    const int d = d_model/h;

    float *QKT;
    {
        dim3 threadsPerBlock(16, 16, 1);
        dim3 blocksPerGrid((N + threadsPerBlock.x - 1) / threadsPerBlock.x,
                          (M + threadsPerBlock.y - 1) / threadsPerBlock.y,
                          h);
        cudaMallocAsync((void **)&QKT, h*M*N*sizeof(float), 0);
        cudaMemsetAsync(QKT, 0, h*M*N*sizeof(float), 0);
        matmul_transposed_kernel<<<blocksPerGrid, threadsPerBlock>>>(Q, K, QKT, M, d,N, h);
    }

    float *row_max;
    {
        cudaMallocAsync((void **)&row_max, h*M*sizeof(float), 0);
        int threadsPerBlock = 256;
        int blocksPerGrid = (h*M + threadsPerBlock - 1)/threadsPerBlock;
        fill_kernel<<<blocksPerGrid,threadsPerBlock>>>(row_max,-INFINITY,h*M);
    }
    {
        dim3 threadsPerBlock(1,256,1);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y, h);
        max_kernel<<<blocksPerGrid,threadsPerBlock,threadsPerBlock.y*sizeof(float)>>>(QKT,row_max,M,N, h);
    }

    float *row_sum;
    {
        cudaMallocAsync((void **)&row_sum, h*M*sizeof(float), 0);
        cudaMemsetAsync(row_sum, 0, h*M*sizeof(float), 0);
        dim3 threadsPerBlock(1,256,1);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y,h);
        expf_and_sum<<<blocksPerGrid, threadsPerBlock, threadsPerBlock.y*sizeof(float)>>>(QKT, row_sum, row_max,M,N,sqrt(d),h);
    }

    {
        dim3 threadsPerBlock(1,256,1);
        dim3 blocksPerGrid(M, (N + threadsPerBlock.y - 1) / threadsPerBlock.y,h);
        divide_kernel<<<blocksPerGrid, threadsPerBlock>>>(QKT, row_sum,M,N,h);
    }

    cudaFreeAsync(row_max, 0);
    cudaFreeAsync(row_sum, 0);

    {
        dim3 threadsPerBlock(16, 16,1);
        dim3 blocksPerGrid((d + threadsPerBlock.x - 1) / threadsPerBlock.x,
                        (M + threadsPerBlock.y - 1) / threadsPerBlock.y,
                        h);
        matmul_kernel<<<blocksPerGrid, threadsPerBlock>>>(QKT, V, output, M, N, d, h);
    }

    cudaFreeAsync(QKT, 0);
    cudaDeviceSynchronize();
}



