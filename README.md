# bellman "Community edition"
 
Originally developed for ZCash, it has diverged now and focuses solely on the [PLONK](https://eprint.iacr.org/2019/953) proof system. Uses our "community edition" pairing for Ethereum's BN256 curve. 

## GPU

This fork contains GPU parallel acceleration to the FFT and Multiexponentation algorithms in the groth16 prover codebase under the compilation features `cuda` and `opencl`.

### Requirements
- NVIDIA or AMD GPU Graphics Driver
- OpenCL

( For AMD devices we recommend [ROCm](https://rocm-documentation.readthedocs.io/en/latest/Installation_Guide/Installation-Guide.html) )

### Environment variables

The gpu extension contains some env vars that may be set externally to this library.

- `BELLMAN_NO_GPU`

    Will disable the GPU feature from the library and force usage of the CPU.

  ```rust
  // Example
  env::set_var("BELLMAN_NO_GPU", "1");
  ```

- `EC_GPU_CUDA_NVCC_ARGS`

    By default the CUDA kernel is compiled for several architectures, which may take a long time. `EC_GPU_CUDA_NVCC_ARGS` can be used to override those arguments. The input and output file will still be automatically set.

  ```console
  // Example for compiling the kernel for only the Ampere architecture.
  // https://docs.nvidia.com/cuda/cuda-compiler-driver-nvcc/index.html#virtual-architecture-feature-list
  EC_GPU_CUDA_NVCC_ARGS="--fatbin --gpu-architecture=sm_86 --generate-code=arch=compute_86,code=sm_86"
  ```

## Features

Allows one to design PLONK circuits with custom gates and lookup tables with junction with [franklin-crypto](https://github.com/matter-labs/franklin-crypto) gadget library. At the moment the lookup argument implies using the lookup over the first three state columns (usually refered as A/B/C) and allows to have simultaneously a gate and a lookup applied on the same row of the trace.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Code Examples:

- [Edcon2019_material](https://github.com/matter-labs/Edcon2019_material)
- [EDCON Workshop record (youtube): Intro to bellman: Practical zkSNARKs constructing for Ethereum](https://www.youtube.com/watch?v=tUY0YGTpehg&t=74s)

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
