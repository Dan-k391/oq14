# Actual exterior second derivatives and Helmholtz equation

`lean/ScalarExteriorSecond.lean` is frozen after a clean direct Lean 4.19.0 check. All eleven selected exports use only `propext`, `Classical.choice`, and `Quot.sound`. Independent full source reviews by the coordinator and the hotspot agent both passed.

Source SHA-256: `7fd53ad2c7cea56dfda1c539855da59e4efa8fb1080fc6573def57a5d7b08827`.

The module first proves a general calculus result for an actual scalar kernel and its actual continuous Fréchet derivative away from the origin. A compact product of a small observation neighborhood and the fixed source ball avoids the origin, so continuity gives a uniform derivative bound there. Multiplication by the integrable source produces the required actual domination. This proves both integrability of the derivative response and differentiation of the literal source integral.

For the outgoing Helmholtz kernel, the derivative hypothesis is discharged by an explicit continuous linear map assembled from its already proved Hessian coordinates. The module obtains the actual full Fréchet derivative of each gradient response and identifies every actual second coordinate derivative of the scalar response with the Hessian convolution. The first-derivative identification is used on a neighborhood, so differentiating that identification is justified.

`response_helmholtz` integrates the actual kernel trace identity and proves the classical scalar Helmholtz equation at every observation point outside the compact support ball. All scalar and Hessian products are proved integrable before sums pass under the integral. The zero-source case is treated separately, so no derivative is used at a kernel singularity.

The source needs only L1 integrability and the stated pointwise compact support condition. No source differentiability, derivative-interchange premise, or scalar PDE assumption is made. Continuous second-order regularity is developed separately in `ScalarExteriorRegularity`.

Complete compiler output, locked dependency metadata, and hashes of the actual recursive local import closure are saved in `lean/scalar-exterior-second-verification.txt` and `lean/scalar-exterior-second-provenance.json`. The compiled olean is available locally.
