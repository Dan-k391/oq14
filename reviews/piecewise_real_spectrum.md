# Independent positive-real volume spectrum audit

Reviewer: continuation_review_sol. Date: 2026-10-20.

Source: `lean/PiecewiseRealSpectrum.lean`.
SHA256: `4F866F0AC10AD94CCA1C8149B332320B9503AD71B25D541A38F4FBF1E7FC02B2`.

Independent pinned Lean 4.19 compilation completed with exit 0. All eight
dependency reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The complete source and complete VolumeAnalyticAlternative source were read,
as were the actual ComplexConvolutionAnalytic volume operator definitions
and its exact real-frequency identification. The required piecewise
uniqueness theorem and its actual Maxwell proof were independently audited
in `reviews/piecewise_maxwell_uniqueness.md`.

The real volume inverse is identified exactly with MaterialField.solution.
For the supplied actual material-cell Partition, compact nonnegative bounded
susceptibility, and actual exterior seed point, the proved homogeneous
Maxwell uniqueness gives actual invertibility at every positive real k.
The exceptional set is defined literally as the nonunits of this actual
complex volume operator; it is therefore disjoint from the positive real
axis. Neither invertibility nor absence of exceptional points is assumed.

The actual complex volume family is analytic by the earlier proved bounded
convolution construction. Analytic inversion at an actual unit therefore
gives operator-valued inverse analyticity at each positive-real point. Open
unit-group preimages give an actual complex ball of regular frequencies
around every such point. Applying a fixed bounded linear evaluation proves
analytic dependence for each fixed L2 datum as well.

Precise scope: the positive real axis and some possibly point-dependent
complex neighborhood of each positive frequency, for coefficients admitting
the stated genuine geometric Partition. No uniform resonance-free strip,
absence of poles throughout a half-plane, negative/zero-frequency result,
or arbitrary rough-material uniqueness is asserted. The local analyticity
results require no artificial spectral gap as an input. They concern the
actual volume operator, without silently identifying it with every modal
or port normalization used elsewhere in the manuscript.

No standalone custom axiom/constant declarations or proof-hole tokens occur
in the new source. No proof source was edited. Independent mathematical and
compiler audit: PASS.
