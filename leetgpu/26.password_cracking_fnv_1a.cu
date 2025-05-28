// URL: https://leetgpu.com/challenges/password-cracking-fnv-1a
// GPU: NVIDIA TESLA T4
// Runtime: 0.00565 ms
#include "solve.h"
#include <cuda_runtime.h>

// if we know that 1<=password_length<=6 then possible combinations are 25^6=244140625


const int maxPasswordLength = 6;

// FNV-1a hash function that takes a byte array and its length as input
// Returns a 32-bit unsigned integer hash value
__device__ unsigned int fnv1a_hash_bytes(const unsigned char* data, int length) {
    const unsigned int FNV_PRIME = 16777619;
    const unsigned int OFFSET_BASIS = 2166136261;
    
    unsigned int hash = OFFSET_BASIS;
    for (int i = 0; i < length; i++) {
        hash = (hash ^ data[i]) * FNV_PRIME;
    }
    return hash;
}

__global__ void fnv1a_hash_kernel(unsigned int target_hash, int password_length, int R, char* output_password,int numCombinations) {

    int idx = (blockIdx.x * blockDim.x) + threadIdx.x;
    if(idx < numCombinations) {
        unsigned char password[maxPasswordLength];
        for(int it=0; it < password_length; ++it) {
            password[it] = 'a' + (idx%26);
            idx = idx/26;
        }

        unsigned int hash_int = fnv1a_hash_bytes(password,password_length);
        for(int i = 1; i < R; ++i) {
            hash_int = fnv1a_hash_bytes((const unsigned char*)&hash_int,4);
        }

        if(hash_int == target_hash) {//threads of other blocks will continue execution 
            memcpy(output_password,password,password_length);
            output_password[password_length] = 0;
        }
    }
}


// output_password is a device pointer
void solve(unsigned int target_hash, int password_length, int R, char* output_password) {
    int numCombinations = pow(26,password_length);
    int threadsPerBlock = 256;
    int blocksPerGrid = (numCombinations + threadsPerBlock - 1)/threadsPerBlock;
    fnv1a_hash_kernel<<<blocksPerGrid,threadsPerBlock>>>(target_hash, password_length, R, output_password,numCombinations);
}
