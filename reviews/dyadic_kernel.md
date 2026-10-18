# Actual dyadic dynamic remainder

Source: `lean/DyadicKernel.lean`. Nine selected exports have compiled with
only `propext`, `Classical.choice`, and `Quot.sound`.

The dyadic kernel is k squared times the actual outgoing scalar kernel
times the coordinate identity, plus the actual Hessian proved in
GreenKernel. Subtracting the static Hessian gives an exact formula with
transverse numerator exp(z)(-z squared+z-1)+1 and radial numerator
exp(z)(z squared-3z+3)-3, where z=i k r. Constant and linear cancellation
is proved algebraically before applying actual exponential Taylor bounds.

For real k and |k|r<=1, the two numerators have norms at most 4|z| squared
and 10|z| squared. The normalized coordinate product has norm at most one.
The exact formula therefore gives the componentwise bound
14 k squared/(4 pi r) for r>0. Both signs of k and k=0 are included.

The channel agent independently read all source and checked the actual
Hessian link, cancellation, constants and scope. No defect was found.
The denominator simplification uses a larger recursion depth for proving
nonzero products; it adds no mathematical premise.

This module proves a local pointwise bound. Local integrability, the
singular distributional source, operator mapping estimates and the Newton
convolution identification are separate formalization obligations.
