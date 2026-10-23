# Actual edge cosine two-jet independence

Frozen source: lean/EdgeCosineJets.lean.
SHA256: C8264F53403CC815CD3393CA568B7CABEE8604647A294D48AC47069F45B3FCAF.
Author final pinned compiler/object PASS: exit 0, no warnings, three reports
using standard foundations only. Log: lean/logs/EdgeCosineJets-final.log.
The compiler emits one non-warning tactic suggestion, Try this: ring_nf.
Independent audit pending.

At points (r,y_j,0) with r nonzero and distinct y_j, the actual annihilating
functional on scalar values and all tangential first/second derivatives of
cos(s*x+t*y) has exactly the six expected cosine/sine terms. Its literal
positive/negative edge exponential expansion is proved. Actual bivariate
packet independence forces all six functional coefficients at every point
to vanish if it vanishes for frequencies in a nonempty real rectangle. No
jet-surjectivity or Fourier uniqueness statement is assumed.

This is the special edge geometry used by the final channel construction,
not a claim for arbitrary planar point configurations. Scalar TE realization,
smooth angular approximation, finite even-harmonic-band realization and
physical incoming power remain separate constructions.
