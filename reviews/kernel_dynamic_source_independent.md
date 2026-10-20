# Independent source audit: outgoing scalar and dyadic source identities

Reviewed the complete frozen `lean/KernelSource.lean` and
`lean/DynamicSource.lean`, together with the singularity, gradient, real
remainder bounds, and Newton Hessian results used by their proofs. No
substantive defect was found.

The scalar proof retains the full distributional Newton Hessian. The
outgoing-minus-static scalar potential, its gradient difference, and its
Hessian difference have the required local integrability. Two applications
of the actual point-singularity integration-by-parts theorem identify the
ordinary Hessian difference as the full weak Hessian of the difference.
Thus the decomposition does not silently discard the atomic Newton term.
Tracing gives the outgoing weak Helmholtz identity with `-test(0)` on the
scalar side. Each exchange of a finite sum and an integral has an explicit
integrability justification.

The dyadic proof uses actual compact smooth tests and their actual
coordinate derivatives. The decomposition is the full static Newton
distribution plus an ordinary locally integrable dynamic remainder.
Mixed derivative commutation is proved for those tests. Its divergence
pairing has the correct sign: summing the dyadic pairing against a first
test derivative gives minus that derivative evaluated at zero. The
gradient-divergence and Laplacian pairings then cancel the second-derivative
atomic terms, yielding exactly
`(curl curl - k²) K = k² I delta`.

These are genuine weak kernel identities. They do not yet assert a bounded
volume integral operator on arbitrary sources, a global scattering
solution, or the channel construction. The available `14 k²/(4 pi r)`
remainder estimate is an entrywise estimate; it has not been interpreted
as a matrix operator norm in this review.

The subsequent complete `KernelConvolution.lean` and `WaveResponse.lean`
sources also pass independent review. Compact source and test supports
confine every nonzero integrand to a difference ball of radius `R+S`.
Truncation of the locally integrable kernel to that ball is genuinely L1;
the source is L1 and the compact smooth test is bounded. This establishes
absolute product integrability before Fubini, rather than postulating the
desired pairing interchange.

The translated test is `f(x+y)`, so its value at zero is exactly `f(y)`.
Translation commutes with the actual test derivatives. Integrating the
dyadic source identity therefore gives the correct source convolution
identity with `+k² I rho`. The decomposition identifies the complete static
Newton response plus the literal ordinary dynamic convolution on the same
test. This audit does not interpret a weak distributional response as an
already constructed pointwise scattering solution.

The complete `MagneticResponse.lean` source was also independently reviewed
and passed. Its literal magnetic convolution is `-i k curl A`, with `A` the
scalar outgoing-potential response. The actual weak test convention gives
`curl E = i k H` and `curl H = -i k (E + rho)`. The scalar Helmholtz source
sign, translation sign, and gradient cancellations agree. Expanded test
products are explicitly integrable before their integrals are separated.
The scope remains compact smooth tests until the local C1 density bridge
is proved.
# Material Maxwell assembly

Independent full source review of `lean/MaterialMaxwell.lean` passes. All compact test products are proved integrable before sums are moved through integrals. The actual volume equation and `MaterialField.material_relation` supply the polarization relation. The proved response identities `curl E = i k H` and `curl H = -i k (E + ρ)` give the correct material equation with ε = 1 + χ. The small-volume specialization uses the proved inverse equation, rather than assuming a scattered-field Maxwell equation. Its compact-smooth test scope is explicit; `RegionalCurlUpgrade` supplies the separate regional C1 upgrade once the actual fields are known to be locally L2.
