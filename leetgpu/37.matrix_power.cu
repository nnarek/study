// URL: https://leetgpu.com/challenges/matrix-power
// GPU: NVIDIA TESLA T4
// Runtime: 2.41353 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void identity_matrix_kernel(float* A, size_t size) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < size && col < size) {
        if (row == col) {
            A[row * size + col] = 1;
        } else {
            A[row * size + col] = 0;
        }
    }
}

__global__ void matmul_kernel(const float* A, const float* B, float* C, size_t size) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < size && col < size) {
        float sum = 0.0f;
        for (int k = 0; k < size; ++k) {
            sum += A[row * size + k] * B[k * size + col];
        }
        C[row * size + col] = sum;
    }
}

void matmul(const float* A, const float* B, float* C, size_t size) {
    dim3 threads(16, 16);
    dim3 blocks((size + threads.x-1 ) / threads.x, (size + threads.y-1) / threads.y);
    matmul_kernel<<<blocks, threads>>>(A, B, C, size);
}


// input, output are device pointers
void solve(const float* input_matrix, float* output_matrix, int size, int n) {
    if(n == 0) {
        dim3 threads(16, 16);
        dim3 blocks((size + threads.x-1 ) / threads.x, (size + threads.y-1) / threads.y);
        identity_matrix_kernel<<<blocks, threads>>>(output_matrix, size);
    } else if(n == 1) {
        cudaMemcpy(output_matrix, input_matrix, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
    } else if(n == 2) {
        matmul(input_matrix, input_matrix, output_matrix, size);
        cudaDeviceSynchronize();
    } else if((n&(n-1)) == 0) { // if n is power of 2 then we can avoid from alocation of two temp buffers
        float* temp_matrix;
        cudaMalloc(&temp_matrix, size * size * sizeof(float));
        float* output = output_matrix;
        float* temp = temp_matrix;
        matmul(input_matrix, input_matrix, output, size);
        n/=4;
        do {
            matmul(output, output, temp, size);
            std::swap(output, temp);
            n/=2;
        } while (0 < n);
        if(output != output_matrix) {
            cudaMemcpyAsync(output_matrix, output, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
        }
        cudaDeviceSynchronize();
        cudaFree(temp_matrix);
    } else {

        float* pow_i_matrix;
        float* temp_matrix;
        cudaMalloc(&pow_i_matrix, size * size * sizeof(float));
        cudaMalloc(&temp_matrix, size * size * sizeof(float));

        float* pow_i = pow_i_matrix;
        float* temp = temp_matrix;
        float* output = NULL;

        cudaMemcpyAsync(pow_i_matrix, input_matrix, size * size * sizeof(float), cudaMemcpyDeviceToDevice);

        for (; 0 < n; ) {
            if(n%2 == 1) {
                if(output == NULL) {
                    output = output_matrix;
                    cudaMemcpyAsync(output, pow_i_matrix, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
                } else {
                    matmul(pow_i_matrix, output, temp, size);
                    std::swap(output, temp);
                }
            }
            n/=2;
            if(n > 0) {
                matmul(pow_i_matrix, pow_i_matrix, temp, size);
                std::swap(pow_i_matrix, temp);
            }
        }
        if(output != output_matrix) {
            cudaMemcpyAsync(output_matrix, output, size * size * sizeof(float), cudaMemcpyDeviceToDevice);
        }
        cudaDeviceSynchronize();

        cudaFree(pow_i_matrix);
        cudaFree(temp_matrix);
    }    
} 
