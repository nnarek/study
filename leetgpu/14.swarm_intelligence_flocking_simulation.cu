// URL: https://leetgpu.com/challenges/swarm-intelligence-flocking-simulation
// GPU: NVIDIA TESLA T4
// Runtime: 1.56103 ms
#include "solve.h"
#include <cuda_runtime.h>


__global__ void simulation_kernel(const float* agents, float* agents_next, int N) {
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < N) {
        float x=agents[4*idx], y=agents[4*idx+1], vx=agents[4*idx+2], vy=agents[4*idx+3];
        float vxsum = 0.0f, vysum = 0.0f;
        size_t num_neighbors = 0;
        for(int nidx = 0; nidx < N; ++nidx) {
            if(nidx == idx) {
                continue;
            }
            float nx=agents[4*nidx], ny=agents[4*nidx+1];
            if((x-nx)*(x-nx)+(y-ny)*(y-ny) < 25.0f) {
                float nvx=agents[4*nidx+2], nvy=agents[4*nidx+3];
                ++num_neighbors;
                vxsum+=nvx;
                vysum+=nvy;
            }
        }
        auto vxnew = vx;
        auto vynew = vy;
        if(num_neighbors > 0) {
            vxnew += ((vxsum/num_neighbors) - vx)*0.05f;
            vynew += ((vysum/num_neighbors) - vy)*0.05f;
        }

        agents_next[4*idx] = x+vxnew;
        agents_next[4*idx+1] = y+vynew;
        agents_next[4*idx+2] = vxnew;
        agents_next[4*idx+3] = vynew;
    }
}

// agents, agents_next are device pointers
void solve(const float* agents, float* agents_next, int N) {
    const int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    simulation_kernel<<<blocksPerGrid, threadsPerBlock>>>(agents, agents_next, N);
    cudaDeviceSynchronize();
}

