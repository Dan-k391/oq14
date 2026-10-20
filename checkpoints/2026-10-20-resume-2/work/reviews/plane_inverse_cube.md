# Actual two-dimensional inverse-cube tail verification

Author: continuation_review_sol. Date: 2026-10-20.

Source: `lean/PlaneInverseCube.lean`.
SHA256: `C39D05DF735FC3993F9038A5653A28A9A805DFB09D2CDA698C4F895910E77916`.

Pinned Lean 4.19 targeted compilation and importable olean emission passed
with exit 0. All ten selected dependency reports use only `propext`,
`Classical.choice`, and `Quot.sound`. Root independently read the complete
source and reran the pinned compiler at this exact hash: exit 0 and all
ten reports standard-only. Independent mathematical and compiler audit: PASS.

Plane is actual two-dimensional Euclidean space with its Lebesgue volume.
The inverse-cube profile is the literal function equal to norm(x)^(-3)
outside the radius-T disk and zero inside. No integral convergence is an
input to the final tail theorem.

The proof first derives genuine integrability of radial functions from
integrability of their one-dimensional radial Jacobian product. It uses
the actual punctured-space/sphere-times-positive-radius measure-preserving
homeomorphism, with radial density r in dimension two. Product integrability
and the weighted-density integrability equivalence supply the converse
direction needed here; removal of the zero singleton is legitimate for
Lebesgue measure. This avoids inferring integrability merely from a formal
Bochner integral identity whose undefined value could be zero.

Multiplication of the actual truncated inverse-cube profile by the radial
Jacobian r gives the truncated inverse-square function. The actual improper
integral on (T,infinity) is 1/T for T>0, and is proved integrable separately.
Consequently the two-dimensional profile is integrable and its actual
integral is diskConstant/T, where diskConstant is twice the Lebesgue area
of the unit disk. This is the usual positive finite 2D polar-area constant;
no normalization of angular measure is postulated.

A complex function on the exterior disk whose actual norm is bounded by
C/norm(x)^3 is therefore integrable there, provided it is AE strongly
measurable. Its absolute integral is at most C*diskConstant/T. This is a
general domination theorem; the Maxwell module supplies its actual field
bound and measurability premises rather than assuming them.

The source contains no standalone custom axiom/constant declarations or
proof-hole tokens. Targeted compiler verification: PASS.
