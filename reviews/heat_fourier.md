# HeatFourier independent checks and exact scope

Source: `lean/HeatFourier.lean`, pinned Lean 4.19.0 and mathlib.

The 26 exported theorems prove an ordinary L1 convolution Fourier identity from the actual Fourier integral and Fubini, Gaussian integrability and normalization, the actual Gaussian multiplier, and the two scale formulas

- Newton kernel: `(4*pi*|x|)^-1 = (2*pi*sqrt(pi))^-1 integral_0^infinity exp(-s^2*|x|^2) ds`, away from zero;
- reciprocal-square symbol: `(4*pi^2*|xi|^2)^-1 = (2*pi*sqrt(pi))^-1 integral_0^infinity Fourier(exp(-s^2*|.|^2))(xi) ds`, away from zero.

The spectral scale substitution is the actual real change of variables `t=s^-2`. The scale integrability conclusions follow from the already computed nonzero integrals and Lean's definition of a nonintegrable Bochner integral as zero. No density, Fourier multiplier, or Newton representation is supplied as an assumption.

The file does not yet assert the distributional Newton Fourier identity. The interchange with a Schwartz pairing requires absolute integrability and is assigned to the next module. It also does not identify the dyadic static convolution with the longitudinal projection.

Independent read-only audit by the hotspots agent passed all formulas, constants, convolution signs, and scope. The author's direct compile passes all 26 declarations; each axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

Related read-only audits performed by the channels agent: root's DyadicKernel9 passes the actual Hessian/remainder identity and its 14*k^2/(4*pi*r) estimate; root's KernelIntegrability10 passes the actual Haar polar-coordinate transfer, inverse-radius local estimates, and Green-kernel L1/L2 conclusions. Neither audit introduced any assumed kernel identity.
