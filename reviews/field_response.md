# Actual convolved Maxwell source and material equations

The root read and developed NewtonWeak5, KernelConvolution6, WaveResponse3,
FieldResponse5, MagneticResponse10 and MaterialMaxwell7. The first five
modules passed direct pinned Lean compilation and emitted importable objects.
MaterialMaxwell's seven reports and final process also passed, and its
importable object was emitted. Channels independently audited its full source. Each selected export uses only
propext, Classical.choice and Quot.sound.

NewtonWeak derives the vanishing actual weak curl of the L2 Newton response
from its proved Fourier symbol and genuine compact-C1 test approximation.
The coordinate transport and inverse-Fourier derivative sign are explicit.
The channels agent independently audited it.

KernelConvolution proves absolute source/test product integrability for a
locally integrable kernel, a compact L1 source and a compact smooth test.
Cutting the kernel beyond the sum of the two support radii is exact.
Fubini, translation of actual tests and commutation of their actual
derivatives then give the literal spatial response pairing.
Channels and counterexamples independently audited it.

WaveResponse convolves the complete dyadic source identity with the actual
source. It preserves the full Newton distribution and the ordinary dynamic
remainder. FieldResponse identifies this action with the constructed spatial
L2 Newton field plus the literal dynamic integrals, proving the actual
curl-curl source equation. Mixed Newton derivatives are explicitly symmetric,
so the column and component indexing agree. Channels independently audited
both; counterexamples also audited WaveResponse.

MagneticResponse constructs H = -ik curl(phi_k * rho) through actual locally
integrable gradient kernels. Integration by parts gives its exact potential
pairing. Commutation of genuine test derivatives cancels the electric
gradient term; the scalar Helmholtz equation gives the remaining source.
Consequently curl E = ik H and curl H = -ik(E + rho) against every compact
smooth test. There is no division by k; these identities also hold at k=0.
All finite sums and split integrals have their integrability established.
Channels and counterexamples independently audited the full source and signs.

MaterialMaxwell combines these source equations with the independently
proved volume-equation relation rho = chi(E_inc + E_scattered). The incoming
field satisfies the vacuum equations; no Maxwell equation for the response
is a premise. The resulting actual total fields satisfy the dielectric
equations with epsilon = 1 + chi. Local integrability of the incident
components justifies addition of pairings. The classical-vacuum implication
uses the existing genuine integration-by-parts theorem.

Scope is exact: the newly constructed field equations in these modules use
compact smooth tests. The C1-test/H(curl) upgrade is a separate proof.
Radiation, arbitrary-size outgoing solvability, scattering completeness,
channel asymptotics and modal resolvent normalization are not inferred from
these equations. Algebraic uniqueness of the volume unknown is not yet a
theorem of uniqueness among all outgoing Maxwell fields.
