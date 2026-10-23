# Actual harmonic-polynomial half-turn projector

Frozen source: lean/HarmonicHalfTurn.lean.
SHA256: 1DF3E21DD42ECAA6981F71CB46CB90BFB5930A89DB8BA4FC53A96BFCD043635B.
Author final pinned compiler/object PASS: exit 0, no warnings, six reports
using standard foundations only. Log: lean/logs/HarmonicHalfTurn-final.log.
Root independent complete-source mathematical review and fresh pinned compiler PASS; no warnings, standard foundations only.

The actual map x -> -R_z x is constructed as an orthogonal linear equivalence,
with norm preservation and involution proved from genuine Euclidean coordinates.
Averaging p with its actual rotated polynomial preserves homogeneity and
harmonicity and gives an exactly half-turn-invariant polynomial. This module
supplies the actual polynomial symmetry projector for restricted TE interpolation;
it does not duplicate generic Maxwell rotation covariance and does not yet
assert even-degree filtering or any finite-power interpolation result.
