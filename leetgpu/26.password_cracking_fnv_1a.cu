// URL: https://leetgpu.com/challenges/password-cracking-fnv-1a
// GPU: NVIDIA TESLA T4
// Runtime: 0.00411 ms
#include "solve.h"
#include <cuda_runtime.h>

// if we know that 1<=password_length<=6 then possible combinations are 25^6=244140625


// FNV-1a hash function that takes a byte array and its length as input
// Returns a 32-bit unsigned integer hash value
template<int length>
__device__ unsigned int fnv1a_hash_bytes(const unsigned char* data) {
    const unsigned int FNV_PRIME = 16777619;
    const unsigned int OFFSET_BASIS = 2166136261;
    
    unsigned int hash = OFFSET_BASIS;
    #pragma unroll 
    for (int i = 0; i < length; i++) {
        hash = (hash ^ data[i]) * FNV_PRIME;
    }
    return hash;
}

template<int password_length>
__global__ void fnv1a_hash_kernel(unsigned int target_hash, int R, char* output_password,int numCombinations, int* found_flag) {
    if(*found_flag == 1) {//no need to do synchronized read because false positive results are not dangerous
        return;
    }
    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < numCombinations) {
        unsigned char password[password_length];
        #pragma unroll 
        for(int it=0; it < password_length; ++it) {
            password[it] = 'a' + (idx%26);
            idx = idx/26;
        }

        unsigned int hash_int = fnv1a_hash_bytes<password_length>(password);
        for(int i = 1; i < R; ++i) {
            hash_int = fnv1a_hash_bytes<4>((const unsigned char*)&hash_int);
        }

        if(hash_int == target_hash) {//threads of other blocks will continue execution 
            memcpy(output_password,password,password_length);
            output_password[password_length] = 0;
            *found_flag = 1;
        }
    }
}


// output_password is a device pointer
template<int password_length>
void solve_for_given_pass_length(unsigned int target_hash, int R, char* output_password) {
    int *found_flag;
    cudaMallocAsync((void **)&found_flag, sizeof(int), 0);
    cudaMemsetAsync(found_flag, 0, sizeof(int),0);

    int numCombinations = pow(26,password_length);
    int threadsPerBlock = 256;
    int blocksPerGrid = (numCombinations + threadsPerBlock - 1)/threadsPerBlock;
    fnv1a_hash_kernel<password_length><<<blocksPerGrid,threadsPerBlock>>>(target_hash, R, output_password,numCombinations,found_flag);
    cudaDeviceSynchronize();  
}
// assuming that password_length can not exceed 6
void solve(unsigned int target_hash, int password_length, int R, char* output_password) {
    switch(password_length) {
        case 1: solve_for_given_pass_length<1>(target_hash,R,output_password); return;
        case 2: solve_for_given_pass_length<2>(target_hash,R,output_password); return;
        case 3: solve_for_given_pass_length<3>(target_hash,R,output_password); return;
        case 4: solve_for_given_pass_length<4>(target_hash,R,output_password); return;
        case 5: solve_for_given_pass_length<5>(target_hash,R,output_password); return;
        case 6: solve_for_given_pass_length<6>(target_hash,R,output_password); return;
    }
}
