# L1KernelOperator verification

Frozen source: `lean/L1KernelOperator.lean`.
SHA256: `B47E1B35A763E38A6650E4E7017EC0CFDED1AE9D59E3C43E2EA1BFB5BBEEF7CD`.

The domain is the actual scalar L1 quotient on three-dimensional Euclidean
Lebesgue space. The codomain is the Banach space of bounded complex-linear
operators on the existing scalar L2 space. Kernel AE representative
independence is proved using the ordinary Fourier integral. Kernel addition
and complex scalar multiplication are also proved for that actual integral
and the existing Fourier multiplier realization, then transferred honestly
through the L1 quotient operations.

The genuine complex-linear map `operator` has operator norm at most one.
Its bound follows from the previously derived literal-convolution Young bound
and the equality between the integral of the representative norm and its L1
norm. It agrees exactly with `L1Convolution.operator q hq` on every actual
integrable kernel `q`. For integrable L2 sources, its values agree almost
everywhere with the literal spatial convolution.

The continuous complex-linear `ballCutoff R` maps global scalar L2 to L1 by
the literal closed-ball indicator. It is constructed using the established
Holder bounded bilinear product of two L2 functions, fixing the actual L2
indicator as its first argument. Its AE formula and equality with the L1
class of any supported actual kernel are proved. `localOperator R` composes
the cutoff with the kernel-to-convolution map and agrees with the actual
convolution operator on each such kernel. This supplies the bounded linear
transfer required for Banach-valued kernel holomorphy.

Pinned Lean 4.19 compile and importable object export completed with exit 0. All 18 selected theorem dependency reports contain only propext, Classical.choice, and Quot.sound. Root independently read the complete source and accepted the construction at the frozen hash above. Source scan clear of proof placeholders or extra foundational declarations.

Root integration removed surplus blank lines at end of file only. The clean aggregate build records the packaged source hash; targeted hashes above remain the original run evidence.

Root subsequently gave final freeze approval at the recorded hash.
