# KernelReciprocity verification

Frozen source: `lean/KernelReciprocity.lean`.
SHA256: `3CA16B0CBA887968767214CFEF4C197B3FC03980C73D9302B1FBAB959CC45D18`.

Pinned Lean 4.19 compilation and object export completed with exit 0. All 29
selected theorem dependency reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The source scan found no proof placeholders or additional
foundational declarations.

The actual dynamic dyadic remainder is even in displacement and symmetric in
its two matrix indices. Closed-ball localization preserves both properties.
For any integrable even scalar kernel and two arbitrary scalar L2 functions,
the literal two-variable product is absolutely integrable. The proof uses the
two integrable convolution products formed from the squared source norms and
the kernel norm, with the elementary product bound. Fubini is therefore
justified for the actual L2 pairing.

The existing Fourier-constructed bounded convolution operator is identified
with its genuine spatial integral on L1 intersection L2. The verified Fubini
identity then extends to all L2 by established Schwartz density and pairing
continuity. Finite coordinate assembly and the actual kernel symmetries give
bilinear reciprocity of `DynamicConvolution.operator` on all vector L2.
The pairing contains no complex conjugation; the conjugate appears only in an
auxiliary inner-product formula establishing continuity.

Root independently read and conceptually accepted the kernel/Fubini/dynamic
chain on October 20, 2026. The scope is the real-frequency remainder response.
There is no reciprocal resonance normalization in this module.


Root completed the final full-source audit at the frozen hash above and accepted the fixed explicit density extension. Final freeze PASS.

Root integration removed surplus blank lines at end of file only. The clean aggregate build records the packaged source hash; targeted hashes above remain the original run evidence.
