# ModalMatchingNorm — actual matching derivative normalization

Source: `lean/ModalMatchingNorm.lean`

SHA256: `D80817A440E6DD1421A9D7E1709FBE0C57CC7371ED3A8591DE361535C585BD42`

Evidence: `lean/logs/modal-matching-norm-check.log`. All 16 selected exports
compiled cleanly with an importable object and only `propext`,
`Classical.choice`, and `Quot.sound`.

The actual spherical matching map is differentiated entry by entry using
the previously established Riccati radial equations. Its explicit
derivative is therefore a derivative of the actual map, rather than a
formal matrix introduced without derivative justification. The actual
determinant derivative is also computed.

At each nonzero determinant zero, a nonzero right kernel vector v and
nonzero left covector w are constructed using a nonzero outgoing state
component. Their exact derivative pairing is w(A'v) = D'. The signs agree
with the project's matching convention, whose actual matching matrix has
determinant minus D. The existing inverse formula uses the corresponding
signed adjugate.

The matching inverse residue is proved exactly equal to
v times w(f)/(w(A'v)). At a simple zero the denominator is nonzero. Scaling
v by a and w by b scales the derivative pairing by ab. A nonzero complex
scalar chosen through the complex logarithm makes the simultaneously
scaled derivative pairing equal one; in that scale the actual inverse
residue is exactly the tensor product of the scaled v and w. The final
export instantiates this normalization at the actual previously constructed
high-quality determinant zeros.

Self-review checked the chain-rule factors n and n squared, both radial
curvature expressions, the signed adjugate convention, the separate
zero-derivative-component pivot, the left kernel equation, derivative
pairing sign, scalar square normalization, and preservation of the residue
under simultaneous scaling. The logarithm is used for a pointwise scalar
choice; continuity or holomorphy of this pivot-dependent choice is not
claimed.

This is a new finite matching-pencil dependency beyond the previous
one-dimensional residue-image statement. It is not yet the manuscript's
physical reciprocal norm N(E) involving the volume Green-kernel derivative.
Identifying those objects still requires the actual volume pencil and
appropriate angular-sector spectral reduction. Root independently read
the complete final source at the recorded hash and passed all 16 exports.
The source is frozen.

## Remaining dependencies found in the manuscript audit

The existing `ModalAlgebraicity` modules reduce a hypothetical multiple
degree pole or common pole at distinct degrees to a nonzero algebraic
complex number whose exponential is algebraic. The cached library has the
Lindemann analytical-part development, but lacks the final
Hermite–Lindemann conclusion needed to turn that obstruction into a
contradiction. Full-sector operator multiplicity would additionally need
the separated vector spherical harmonic and Fredholm identification; it
does not follow solely from matching-matrix simplicity.

The conical construction in `modal_next.tex` depends on an actual
axisymmetric odd H1(S2) weighted angular eigenbranch, its compact spectral
projection, and a coefficient topology surviving the exponent-one limit.
None is supplied by the matching normalization module, a scalar Rayleigh
trial inequality, or driven Runge approximation. The physical volume norm,
continued eigenbranch, conical coefficient existence, and final finite
modal hotspot packing remain separate formal obligations.
