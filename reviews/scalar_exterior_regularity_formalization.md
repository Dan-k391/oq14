# Genuine exterior C2 regularity

`lean/ScalarExteriorRegularity.lean` is frozen after a clean direct Lean 4.19.0 check. Its six selected exports use only `propext`, `Classical.choice`, and `Quot.sound`. The hotspot agent's independent full source review passed.

Source SHA-256: `af076272f72ad315d64cf2498fdd35c3c73b5a1d8651a42f8a72b1f3363d3d94`.

The module proves continuity of the actual continuous-linear-map-valued derivative response by dominated integration on the source support. The common local bound is constructed from continuity away from the origin and the positive exterior gap. It then proves C1 regularity for kernels whose actual derivatives satisfy these hypotheses, and discharges the hypotheses for each outgoing Helmholtz gradient kernel using the actual Hessian.

The potential's actual Fréchet derivative is identified with the finite sum of its gradient responses times the fixed coordinate maps. Each scalar gradient response is C1, so that derivative map is C1. The already proved derivative identities therefore establish `ContDiffAt ℝ 2` at every exterior point, and `ContDiffOn ℝ 2` on the entire exterior open set.

The proof explicitly supplies continuity on a neighborhood where the mathlib C0-at definition requires it. It does not substitute pointwise continuity for neighborhood regularity. Source assumptions remain actual L1 integrability and pointwise vanishing outside the fixed compact ball.

This completes the C2 scalar-potential layer; it does not by itself establish third derivatives, full smoothness, or classical derivatives of the dyadic electric field.

Complete compiler output, lock metadata, and hashes of the actual local import closure are saved in `lean/scalar-exterior-regularity-verification.txt` and `lean/scalar-exterior-regularity-provenance.json`. The local olean is ready.
