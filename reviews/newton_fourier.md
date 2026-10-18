# NewtonFourier: actual Newton kernel Fourier identification

`lean/NewtonFourier.lean` proves eleven exported theorems in pinned Lean 4.19.0. Every axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`; the complete file compiles without warnings or errors.

The final identity, for every complex Schwartz function f, is

`integral N(x) Fourier(f)(x) dx = integral (4*pi^2*|xi|^2)^-1 f(xi) dxi`,

where N is the actual previously defined Newton kernel `GreenKernel.phi 0`. An inverse-Fourier pairing corollary is also proved.

The proof uses the actual local inverse-radius estimates from KernelIntegrability, boundedness of Schwartz functions on the unit ball, and their L1 tails. Both Gaussian scale-space products are proved absolutely integrable. Fubini is applied only after those proofs. The scale formulas from HeatFourier and the actual bilinear Fourier integral interchange then give the result. The source point is removed only on a null set, without removing any nontrivial neighborhood.

The spectral coefficient is exactly `sqrt(pi)/(2*pi)` in the scale-integral norm estimate and exactly `1/(4*pi^2*|xi|^2)` in the final symbol. The Fourier convention is `exp(-2*pi*i*inner(x,xi))`.

Independent read-only review by the hotspots agent passed the complete file, all constants, singularity/tail estimates, absolute-Fubini steps, and inversion. No substantive defect was found.

Scope: this establishes the scalar distributional Fourier identity through all Schwartz pairings. The distributional Hessian and its convolution identification with the physical longitudinal projection are subsequent steps; neither is assumed here. In particular, the pointwise Hessian alone is not substituted for the distributional Hessian at the source.
