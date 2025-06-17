// URL: https://leetgpu.com/challenges/k-means-clustering
// GPU: NVIDIA TESLA T4
// Runtime: 1.23731 ms
#include "solve.h"
#include <cuda_runtime.h>

__global__ void find_nearest_centroids_kernel(const float* data_x, const float* data_y, int* labels,
                                        const float* centroids_x, const float* centroids_y, int sample_size, int k) {
    int point_id = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(point_id < sample_size) {
        int nearest_centroid_index = 0;
        float min_distance_sq = INFINITY;
        for(int centroid_index = 0; centroid_index < k; ++centroid_index) {
            auto x = centroids_x[centroid_index] - data_x[point_id];
            auto y = centroids_y[centroid_index] - data_y[point_id];
            if(x*x + y*y < min_distance_sq) {
                min_distance_sq = x*x + y*y;
                nearest_centroid_index = centroid_index;
            }
        }
        labels[point_id] = nearest_centroid_index;
    }
}

__global__ void recalculate_centroid_kernel(const float* data_x, const float* data_y, const int* labels,
                                    int* centroid_point_nums, float* new_centroids_x, float* new_centroids_y,
                                    int sample_size, int k) {
    __shared__ float new_centroids_x_shared[100];
    __shared__ float new_centroids_y_shared[100];
    __shared__ int centroid_point_nums_shared[100];

    if(threadIdx.x < k) {
        new_centroids_x_shared[threadIdx.x] = 0;
        new_centroids_y_shared[threadIdx.x] = 0;
        centroid_point_nums_shared[threadIdx.x] = 0;
    }
    __syncthreads();

    int point_id = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(point_id < sample_size) {
        const auto centroid_id = labels[point_id];

        atomicAdd(new_centroids_x_shared + centroid_id, data_x[point_id]);
        atomicAdd(new_centroids_y_shared + centroid_id, data_y[point_id]);
        atomicAdd(centroid_point_nums_shared + centroid_id, 1);
    }
    
    __syncthreads();

    if(threadIdx.x < k) {
        atomicAdd(new_centroids_x + threadIdx.x, new_centroids_x_shared[threadIdx.x]);
        atomicAdd(new_centroids_y + threadIdx.x, new_centroids_y_shared[threadIdx.x]);
        atomicAdd(centroid_point_nums + threadIdx.x, centroid_point_nums_shared[threadIdx.x]);
    }
}

__global__ void finalize_recalculation_and_compare_kernel(const int* centroid_point_nums, float* new_centroids_x, float* new_centroids_y,
                                                            const float* prev_centroids_x, const float* prev_centroids_y, 
                                                            int k, int* num_converged_centroids) {
    const int idx = threadIdx.x;
    if(idx == 0) {
        *num_converged_centroids = 0;
    }        
    __syncthreads();                                                 
    if(idx < k) {
        const int count = centroid_point_nums[idx];
        if (count > 0) {
            new_centroids_x[idx] /= count;
            new_centroids_y[idx] /= count;
        } else {
            new_centroids_x[idx] = prev_centroids_x[idx];
            new_centroids_y[idx] = prev_centroids_y[idx];
        }

        const auto x_diff = new_centroids_x[idx] - prev_centroids_x[idx];
        const auto y_diff = new_centroids_y[idx] - prev_centroids_y[idx];
        if(x_diff*x_diff + y_diff*y_diff < 1.0e-8f) {
            atomicAdd(num_converged_centroids,1);
        }
    }
}

// data_x, data_y, labels, initial_centroid_x, initial_centroid_y,
// final_centroid_x, final_centroid_y are device pointers 
void solve(const float* data_x, const float* data_y, int* labels,
           float* initial_centroid_x, float* initial_centroid_y,
           float* final_centroid_x, float* final_centroid_y,
           int sample_size, int k, int max_iterations) {
    int threadsPerBlock = 256;
    int blocksPerGrid = (sample_size + threadsPerBlock - 1) / threadsPerBlock;

    int* centroid_point_nums = NULL;
    cudaMallocAsync((void**)&centroid_point_nums, k*sizeof(int), 0);

    int* num_converged_centroids = NULL;
    cudaMallocAsync((void**)&num_converged_centroids, sizeof(int), 0);

    auto* prev_centroid_x = final_centroid_x;
    auto* prev_centroid_y = final_centroid_y;
    auto* new_centroid_x = initial_centroid_x;
    auto* new_centroid_y = initial_centroid_y;

    for(int i = 0; i < max_iterations; ++i) {
        std::swap(new_centroid_x,prev_centroid_x);
        std::swap(new_centroid_y,prev_centroid_y);

        find_nearest_centroids_kernel<<<blocksPerGrid, threadsPerBlock>>>(data_x, data_y, labels,
                                                                    prev_centroid_x, prev_centroid_y,
                                                                    sample_size, k);

        cudaMemsetAsync(centroid_point_nums,0,k*sizeof(int));
        cudaMemsetAsync(new_centroid_x,0,k*sizeof(float));
        cudaMemsetAsync(new_centroid_y,0,k*sizeof(float));
        recalculate_centroid_kernel<<<blocksPerGrid, threadsPerBlock>>>(data_x, data_y, labels,
                                        centroid_point_nums, new_centroid_x, new_centroid_y,
                                        sample_size, k);

        finalize_recalculation_and_compare_kernel<<<1,128>>>(centroid_point_nums, new_centroid_x, new_centroid_y,
                                                             prev_centroid_x, prev_centroid_y,k,num_converged_centroids);
        int num_converged_centroids_host;
        cudaMemcpyAsync(&num_converged_centroids_host,num_converged_centroids,sizeof(int),cudaMemcpyDeviceToHost);
        
        cudaDeviceSynchronize();
        if(num_converged_centroids_host == k) {
            break;
        }
    }
    if(new_centroid_x != final_centroid_x) {
        cudaMemcpy(final_centroid_x,new_centroid_x,k*sizeof(float),cudaMemcpyDeviceToDevice);
        cudaMemcpy(final_centroid_y,new_centroid_y,k*sizeof(float),cudaMemcpyDeviceToDevice);
    }

    cudaFree(centroid_point_nums);
    cudaFree(num_converged_centroids);
}

