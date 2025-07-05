// URL: https://leetgpu.com/challenges/sparse-matrix-vector-multiplication
// GPU: NVIDIA TESLA T4
// Runtime: 2.41639 ms
#include "solve.h"
#include <cuda_runtime.h>

struct item_t {
    float val;
    short row;
    short col;
};

__global__ void compress_mat_kernel(const float* mat, item_t* compressed_mat, int M, int N, int* last_index) {
    __shared__ int numZerosInBlock;
    __shared__ int index_start;

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    int idy = (blockIdx.y * blockDim.y) + threadIdx.y;
    if(threadIdx.y == 0) {
        numZerosInBlock = 0;
    }
    __syncthreads();
    if(idx < M && idy < N) {
        const auto val = mat[idx*N + idy];
        int local_index = -1;
        if(val != 0.0f) {
            local_index = atomicAdd(&numZerosInBlock,1);
        }
        __syncthreads();
        
        if(threadIdx.y == 0) {
            index_start = atomicAdd(last_index,numZerosInBlock);
        }
        __syncthreads();
        if(local_index != -1) {
            compressed_mat[index_start + local_index] = {val, (short)idx, (short)idy};
        }
    }
}

__global__ void matvec_kernel(const item_t* compressed_mat, const float* v, float* y, int nnz) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < nnz) {
        auto item = compressed_mat[idx];
        atomicAdd(y + item.row, item.val*v[item.col]);
    }
}

void solve(const float* mat, const float* v, float* y, int M, int N, int nnz) {
    item_t* compressed_mat;
    cudaMalloc(&compressed_mat, nnz * sizeof(item_t));
    int* last_index;
    cudaMalloc(&last_index, sizeof(int));
    cudaMemset(last_index, 0, sizeof(int));
    cudaMemset(y, 0, M * sizeof(float));
    {
        dim3 threadsPerBlock(1,256);
        dim3 blocksPerGrid((M + threadsPerBlock.x - 1) / threadsPerBlock.x,
                           (N + threadsPerBlock.y - 1) / threadsPerBlock.y);
        compress_mat_kernel<<<blocksPerGrid, threadsPerBlock>>>(mat, compressed_mat, M, N, last_index);
    }
    {
        dim3 threadsPerBlock(256);
        dim3 blocksPerGrid((nnz + threadsPerBlock.x - 1) / threadsPerBlock.x);
        matvec_kernel<<<blocksPerGrid, threadsPerBlock>>>(compressed_mat, v, y, nnz);
    }
    cudaDeviceSynchronize();
    cudaFree(compressed_mat);
} 
