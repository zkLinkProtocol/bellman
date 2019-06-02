#![feature(test)]

#[cfg(feature = "gpu")]
mod benchmark_gpu{

    extern crate rand;
    extern crate test;
    extern crate bellman_ce as bellman;

    use bellman::ff::Field;
    use bellman::Engine;
    use bellman::SynthesisError;
    use bellman::{Circuit, ConstraintSystem};
    use bellman::pairing::bn256::{Bn256};

    const MIMC_ROUNDS: usize = 10000;

    /// This is an implementation of MiMC, specifically a
    /// variant named `LongsightF322p3` for BLS12-381.
    /// See http://eprint.iacr.org/2016/492 for more 
    /// information about this construction.
    ///
    /// ```
    /// function LongsightF322p3(xL ⦂ Fp, xR ⦂ Fp) {
    ///     for i from 0 up to 321 {
    ///         xL, xR := xR + (xL + Ci)^3, xL
    ///     }
    ///     return xL
    /// }
    /// ```
    fn mimc<E: Engine>(
        mut xl: E::Fr,
        mut xr: E::Fr,
        constants: &[E::Fr]
    ) -> E::Fr
    {
        assert_eq!(constants.len(), MIMC_ROUNDS);

        for i in 0..MIMC_ROUNDS {
            let mut tmp1 = xl;
            tmp1.add_assign(&constants[i]);
            let mut tmp2 = tmp1;
            tmp2.square();
            tmp2.mul_assign(&tmp1);
            tmp2.add_assign(&xr);
            xr = xl;
            xl = tmp2;
        }

        xl
    }

    /// This is our demo circuit for proving knowledge of the
    /// preimage of a MiMC hash invocation.
    #[derive(Clone)]
    struct MiMCDemo<'a, E: Engine> {
        xl: Option<E::Fr>,
        xr: Option<E::Fr>,
        constants: &'a [E::Fr]
    }

    /// Our demo circuit implements this `Circuit` trait which
    /// is used during paramgen and proving in order to
    /// synthesize the constraint system.
    impl<'a, E: Engine> Circuit<E> for MiMCDemo<'a, E> {
        fn synthesize<CS: ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), SynthesisError>
        {
            assert_eq!(self.constants.len(), MIMC_ROUNDS);

            // Allocate the first component of the preimage.
            let mut xl_value = self.xl;
            let mut xl = cs.alloc(|| "preimage xl", || {
                xl_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            // Allocate the second component of the preimage.
            let mut xr_value = self.xr;
            let mut xr = cs.alloc(|| "preimage xr", || {
                xr_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            for i in 0..MIMC_ROUNDS {
                // xL, xR := xR + (xL + Ci)^3, xL
                let cs = &mut cs.namespace(|| format!("round {}", i));

                // tmp = (xL + Ci)^2
                let tmp_value = xl_value.map(|mut e| {
                    e.add_assign(&self.constants[i]);
                    e.square();
                    e
                });
                let tmp = cs.alloc(|| "tmp", || {
                    tmp_value.ok_or(SynthesisError::AssignmentMissing)
                })?;

                cs.enforce(
                    || "tmp = (xL + Ci)^2",
                    |lc| lc + xl + (self.constants[i], CS::one()),
                    |lc| lc + xl + (self.constants[i], CS::one()),
                    |lc| lc + tmp
                );

                // new_xL = xR + (xL + Ci)^3
                // new_xL = xR + tmp * (xL + Ci)
                // new_xL - xR = tmp * (xL + Ci)
                let new_xl_value = xl_value.map(|mut e| {
                    e.add_assign(&self.constants[i]);
                    e.mul_assign(&tmp_value.unwrap());
                    e.add_assign(&xr_value.unwrap());
                    e
                });

                let new_xl = if i == (MIMC_ROUNDS-1) {
                    // This is the last round, xL is our image and so
                    // we allocate a public input.
                    cs.alloc_input(|| "image", || {
                        new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                    })?
                } else {
                    cs.alloc(|| "new_xl", || {
                        new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                    })?
                };

                cs.enforce(
                    || "new_xL = xR + (xL + Ci)^3",
                    |lc| lc + tmp,
                    |lc| lc + xl + (self.constants[i], CS::one()),
                    |lc| lc + new_xl - xr
                );

                // xR = xL
                xr = xl;
                xr_value = xl_value;

                // xL = new_xL
                xl = new_xl;
                xl_value = new_xl_value;
            }

            Ok(())
        }
    }

    // #[cfg(feature = "gpu")]
    #[bench]
    fn bench(b: &mut test::Bencher) {
        use bellman::groth16::generate_random_parameters;
        use bellman::groth16_gpu::{create_random_proof};
        use rand::{Rng, XorShiftRng, SeedableRng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

        println!("Creating parameters...");

        // Create parameters for our circuit
        let params = {
            let c = MiMCDemo::<Bn256> {
                xl: None,
                xr: None,
                constants: &constants
            };

            let params = generate_random_parameters(c, rng).unwrap();

            use bellman_ce::groth16_gpu::GpuParameters;

            GpuParameters::from_parameters(params)
        };

        println!("Done creating parameters...");

        let xl = rng.gen();
        let xr = rng.gen();
        let _image = mimc::<Bn256>(xl, xr, &constants);

        let c = MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants
        };

        b.iter(|| {
            create_random_proof(c.clone(), &params, rng).unwrap()
        });
    }
}