# bellman "Community edition"
 
Originally developed for ZCash, with extensions from us to make it a little more pleasant. Uses our "community edition" pairing for Ethereum's BN256 curve. Now published as `bellman_ce` on `crate.io` to allow ease of use.

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

There are two available features to be used in production and are stable and will not be changed in terms of API. Those are Groth16 proof system implementation.

- `multicore` feature (enabled by default) is intended to be run on PC and in environments that have support of a full `std` including threading.
- `singlecore` feature is mainly intended for WASM systems, where non-compatible external crates are removed, along with all the multithreading.

Due to request to have a maintainable repo with WASM compatibility those features were implemented during the implementation of GM17 and SONIC proof systems. That's why there are two more features that are incomplete and will have breaking changes in a future. Those are for interested enthusiasts.

- `gm17` - is incomplete and most likely will get attention after putting SONIC to completeness.
- `sonic` - 90% complete. Original implementation of `helped` protocol is integrated with API similar to the Groth16, along with wrapping adapters to use existing circuits without any changes. `unhelped` version is not yet complete, but all cryptographical primitives are implemented and tested. Right now it's a priority.

## Future progress

It's intended to add `GM17` proof system and `SONIC` proof system.

## Features

There are two available features to be used in production and are stable and will not be changed in terms of API. Those are Groth16 proof system implementation.

- `multicore` feature (enabled by default) is intended to be run on PC and in environments that have support of a full `std` including threading.
- `singlecore` feature is mainly intended for WASM systems, where non-compatible external crates are removed, along with all the multithreading.

Due to request to have a maintainable repo with WASM compatibility those features were implemented during the implementation of GM17 and SONIC proof systems. That's why there are two more features that are incomplete and will have breaking changes in a future. Those are for interested enthusiasts.

- `gm17` - is incomplete and most likely will get attention after putting SONIC to completeness.
- `sonic` - 90% complete. Original implementation of `helped` protocol is integrated with API similar to the Groth16, along with wrapping adapters to use existing circuits without any changes. `unhelped` version is not yet complete, but all cryptographical primitives are implemented and tested. Right now it's a priority.

## Future progress

It's intended to add `GM17` proof system and `SONIC` proof system.

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
