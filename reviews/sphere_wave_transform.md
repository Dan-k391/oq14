# Actual complex sphere-wave transform

Frozen source: lean/SphereWaveTransform.lean.
SHA256: C546FCC4894E9535DBA9AE13D5E81A2086FA619730211F0E8A8F293C9E4A268E.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all eight reports standard-only. Log: lean/logs/SphereWaveTransform-final.log.
Independent audit pending.

The actual Euclidean volume-to-sphere measure is used throughout. Its
complex axial integral formula follows from the existing actual
measure-preserving coordinate map and genuine product integrability.
The actual exponential sphere-wave is integrable and its literal integral
is invariant under every orthogonal linear isometry. An actual reflection
aligns any vector to its radius times the third coordinate basis vector;
there is no supplied rotational-symmetry conclusion.

The axial exponential integral is evaluated with the genuine interval
antiderivative. This proves the actual scalar sphere-wave integral equals
8*pi^2/(I*k) times (phi(k,x)-phi(-k,x)) when k and x are nonzero.
This is equivalently 4*pi*sin(k*norm(x))/(k*norm(x)).

The statement concerns the actual scalar sphere integral. Differentiating
it to identify the dyadic sphere integral, deriving actual magnetic parity
and whole-plane tails, and identifying a physical finite-stack Green
tensor remain further constructions.
Root independent complete-source mathematical review and pinned compiler PASS: no warnings, all eight reports standard-only (October 22, 2026).

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `c546fcc4894e9535dba9ae13d5e81a2086fa619730211f0e8a8f293c9e4a268e`. Independent log `lean/logs/SphereWaveTransform-root-audit.log`, SHA256 `bf85134044c3f79d86d573b7eeaab2165b810bb0ea7d7b5f82d0cfb97558c153`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
