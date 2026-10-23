# Whole-plane actual free-volume/parity-density coherent bounds

Frozen source: lean/SourceParityWhole.lean.
SHA256: CA58025A43E22D9386AAD9EE94E26BF18C9A52EA658F741C59921EE591FDBD20.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/SourceParityWhole-final.log.
Independent audit pending.

Actual free-volume electric field against actual magnetic parity density,
and actual electric parity density against actual free magnetic field,
have genuine disk and whole-plane L1 bounds. Disk estimates use the real
parity density entry bound together with the sharp actual free field disk
integrals. Their genuine uniform inverse-cube tails prove whole-plane
integrability. The constants are exactly SourceHerglotzWhole.electricConstant
and magneticConstant times the product of actual source L1 masses. The first
constant grows as 1/d and the second logarithmically on d<=T+R.

No free/parity field identity, density substitution, integrability, tail or
flux bound is assumed. Source support and positive actual plane separation
remain explicit. These estimates provide the gained total reaction flux
terms; physical finite radial-stack Green identification is separate.
