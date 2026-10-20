# NewtonReciprocity verification

Frozen source: `lean/NewtonReciprocity.lean`.
SHA256: `F47CDB7E13D11F7E389ED8217D7A962C700B8FEF27417F0EA983BB47BFD0E124`.

Pinned Lean 4.19 compilation and object export completed with exit 0. All 16
selected theorem dependency reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The source scan found no proof placeholders or additional
foundational declarations.

The full distributional Newton Hessian is retained. Its existing literal
Newton-kernel test action and derived Fourier formula are used directly.
Frequency reflection, evenness, and matrix transpose symmetry prove reciprocity
on actual Schwartz sources. Established vector Schwartz density and continuous
bilinear pairing extend this identity to the actual bounded Newton operator
on all vector L2. The source contribution has not been removed.

Pointwise square-root material multiplication is bilinearly symmetric. The
existing weighted dynamic remainder, static block, and complete
`DynamicVolume.volumeBlock` are consequently bilinearly reciprocal. The exact
`LocalVolumeResponse.localRepresentative` is reciprocal as well.

For two actual compact L2 sources, equality of the local representative and
the untruncated `FieldResponse.electric` on a ball, together with the other
source vanishing outside that ball, transfers the paired integrands globally.
Their products are integrable by scalar L2 product integrability. The final
`electric_compact_L2_reciprocity` proves the actual non-Hermitian electric-source
pairing identity; source L1 integrability is derived from compact support and
L2, rather than required as an additional premise.

Root independently read and conceptually accepted the Newton and actual
compact-response chains on October 20, 2026. The scope is real frequency and
compact L2 sources. Reciprocal resonance normalization is not claimed.


Root completed the final full-source audit at the frozen hash above, including the actual compact L2 electric-field reciprocity bridge. Final freeze PASS.

Root integration removed surplus blank lines at end of file only. The clean aggregate build records the packaged source hash; targeted hashes above remain the original run evidence.
