# Scalar outgoing kernel: exact formal coverage

`lean/GreenKernel.lean` defines exp(i k r)/r and its first two actual real
derivatives, then defines phi(x)=exp(i k |x|)/(4 pi |x|) on Euclidean
three-space. The real Frechet derivative of the norm and the normalized
coordinate are proved, and the chain/product rules give the exact gradient
and Hessian. Local equality away from zero identifies the Hessian with the
actual second partial derivative, rather than just a symbolic expression.
Summing its diagonal and the proved coordinate square identity gives the
three-dimensional scalar Helmholtz equation away from the origin. The
kernel is proved C-infinity there. For real k, its radial exponential has
unit modulus, and the exact remainder r(g'-ikg)=-exp(ikr)/r proves the
Sommerfeld limit.

All seventeen selected exports compiled with only propext, Classical.choice
and Quot.sound. Source SHA256:
`721730a853cff1a637c64b33326ac7742ad0f764cb2a93c4099c57cf07056642`.

The hotspot agent independently read the full source and checked derivative
indices, the 2/r radial trace factor, normalization, Helmholtz sign and
radiation remainder. No defect was found. This theorem does not assert the
distributional delta at the origin, convolution bounds, Maxwell scattering
existence or uniqueness. Those remain explicit additional obligations.
