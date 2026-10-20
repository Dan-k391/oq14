# Actual outgoing scalar and dyadic sources

The October20 batch adds PointSingularity9, RealKernelBounds7,
KernelGradient6, KernelSource13 and DynamicSource7. All selected exports
passed direct Lean4.19 compilation with only propext, Classical.choice and
Quot.sound. Exact source hashes are recorded in the aggregate build provenance.
The counterexamples agent independently read and accepted all five modules;
channels also independently reviewed PointSingularity.

PointSingularity constructs the actual volume-preserving coordinate split.
Except for the null transverse singleton, a whole coordinate line misses the
origin. Genuine integrability of the three products permits Fubini and the
ordinary one-dimensional integration-by-parts theorem. Compact tests and local
integrability discharge the product hypotheses in the weak-partial theorem.

RealKernelBounds uses Taylor bounds at small argument and direct polynomial
bounds at large argument to obtain the actual remainder bound
14k²/(4 pi |x|) at all real frequencies and radii. It derives local L1
integrability, including the outgoing-minus-static pointwise Hessian.
KernelGradient separately proves gradient bounds and local L1 before applying
point removal to the actual scalar outgoing kernel's first weak derivative.

KernelSource applies integration by parts twice to phi_k-N. Its weak Hessian
is exactly the locally integrable pointwise Hessian difference. Adding back
the full Newton distribution therefore preserves the contact source. The
trace of the difference equals -k² phi_k away from zero; actual local L1 and
compact tests justify summation/integration. NewtonHessian supplies the
remaining -test(0), proving the exact outgoing weak Helmholtz equation.

DynamicSource uses compact smooth Schwartz tests, closed under actual
coordinate derivatives. The dyadic action is k² I phi_k plus the full weak
Hessian. Its decomposition includes the full Newton Hessian and the ordinary
dynamic remainder, with integrability checked before splitting the integral.
Commutation of actual mixed derivatives gives the divergence and Laplacian
pairings. The gradient-divergence minus Laplacian expression cancels the
second derivative source terms and leaves exactly k² I delta_0 in
(curl curl-k²)K. The signs were independently checked.

These are actual distributional source identities. They do not themselves
construct the bounded dynamic convolution operator, a solution of the material
volume equation, global radiation, scattering completeness or modal poles.
