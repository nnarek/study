// URL: https://leetgpu.com/challenges/categorical-cross-entropy-loss
// GPU: NVIDIA TESLA T4
// Runtime: 0.35379 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void loss_kernel(const float* logits, const int* true_labels, float* loss, int N, int C) {
    int j = blockIdx.x*blockDim.x + threadIdx.x;
    if(j < N) {
        float exp_sum = 0.0f;
        for(int k = 0; k < C; ++k) {
            exp_sum += expf(logits[j*C+k]);
        }
        const float loss_j = logf(exp_sum) - logits[j*C+true_labels[j]];
        atomicAdd(loss,loss_j);
    }
}
__global__ void div_kernel(float* a, int b) {
    *a /= b;
}

void solve(const float* logits, const int* true_labels, float* loss, int N, int C) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    loss_kernel<<<blocksPerGrid, threadsPerBlock>>>(logits,true_labels,loss,N,C);
    div_kernel<<<1,1>>>(loss, N);
    cudaDeviceSynchronize();
}
