# Differentiation of actual sphere waves

Frozen source: lean/SphereWaveCalculus.lean.
SHA256: 9D2092E1177448B750782634B5AD6411D66D8D71121A7E4C4CCA385C96867727.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all nine reports standard-only. Log: lean/logs/SphereWaveCalculus-final.log.
Independent audit pending.

The actual real Frechet phase map and its operator norm bound are derived
from the unit-sphere norm. The literal complex exponential has the derived
Frechet derivative. Continuous, bounded actual sphere amplitudes give
integrable weighted moments. Differentiation under the genuine finite
surface integral is discharged with the actual phase derivative bound,
measurability and constant integrable domination. Evaluation on a genuine
coordinate basis yields the actual coordinate-moment derivative formula.
Actual coordinate amplitudes are continuous and bounded by one.

The bounded amplitude premise is for this generic integral lemma; its
coordinate instances are derived, not assumed. Dyadic/magnetic parity
identification and coherent whole-plane tails are further constructions.


## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 9 reports use only standard foundations. Final source SHA256 `9d2092e1177448b750782634b5ad6411d66d8d71121a7e4c4cca385c96867727`. Independent log `lean/logs/SphereWaveCalculus-root-audit.log`, SHA256 `c6c6ba8d0dea969bfbd48493df8fc3aac3fb8b083a69f0de459795c9c46df259`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
