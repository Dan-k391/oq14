# Actual exterior scalar derivatives

`lean/ScalarExterior.lean` is frozen after a clean direct Lean 4.19.0 check. All ten selected exports use only `propext`, `Classical.choice`, and `Quot.sound`. Independent full source reviews by the coordinator and the hotspot agent both passed.

Source SHA-256: `c888345be5c2830bdaec7b3f32c2615919260280c35446727c7964ec2b31ff7c`.

For an actual integrable complex source ρ that vanishes outside a closed ball of radius R, `response_hasFDerivAt` proves real Fréchet differentiability of the actual outgoing scalar convolution at every point with `R < ‖x‖`. Its derivative is the actual Bochner integral of the source times a continuous linear map assembled from the three explicit kernel-gradient coordinates.

The proof constructs a ball around the observation point separated uniformly from every point of the source support. The explicit inverse-distance gradient estimate supplies an integrable source-weighted bound for every derivative in that ball. The actual mathlib dominated parameter-integral theorem then proves differentiation under the integral, including the zero-source case without requiring differentiability at the kernel singularity. Derivative integrability is separately established before evaluating the linear map under the integral.

`response_partial` identifies the genuine coordinate derivatives with the gradient-kernel source responses. `response_sommerfeld_limit` consequently proves, for each coordinate j and every path γ whose norm tends to infinity,

`‖γ(t)‖ [∂j u(γ(t)) − ik γj(t)/‖γ(t)‖ u(γ(t))] → 0`.

This is the coordinate outgoing derivative condition. The file does not separately state the radial directional-derivative corollary or the vector Silver–Müller condition. It assumes neither source smoothness nor a radiation condition, and requires no global L2 field.

Complete compiler output, compiler version, locked dependency metadata, and hashes of the actual local import closure are saved in `lean/scalar-exterior-verification.txt` and `lean/scalar-exterior-provenance.json`. The emitted olean is available in the local build cache.
