fn main() {
  gpu_kernel();
}
/// The build script is used to generate the CUDA kernel and OpenCL source at compile-time, if the
/// `cuda` and/or `opencl` feature is enabled.

use pairing::bn256::{G1Affine, G2Affine, Fq, Fq2, Fr};

#[cfg(any(feature = "cuda", feature = "opencl"))]
fn gpu_kernel() { 
  //use blstrs::{Fp, Fp2, G1Affine, G2Affine, Scalar};
  use ec_gpu_gen::SourceBuilder;

  let source_builder = SourceBuilder::new()
      .add_fft::<Fr>()
      .add_multiexp::<G1Affine, Fq>()
      .add_multiexp::<G2Affine, Fq2>();
  ec_gpu_gen::generate(&source_builder);
}

#[cfg(not(any(feature = "cuda", feature = "opencl")))]
fn gpu_kernel() {}
