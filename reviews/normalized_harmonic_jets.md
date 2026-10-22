# Genuine normalized harmonic coefficients and compact spatial jets

Source: `lean/NormalizedHarmonicJets.lean`.
SHA256: `C1151E2D425429397A7DDFA169E12778A73259005E6B35E24230CF2539C79DDE`.

Author final target plus object compiler exit 0, no warnings. Object 295320 bytes. Nine selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/NormalizedHarmonicJets-final.log`.

Every polynomial representative is the actual one constructed from the genuine L2-orthonormal degree-l harmonic basis. Actual addition and rank<=cubic give |Y_li(n)|<=K_l=sqrt((l+1)^3/angularArea), with no angular basis or normalization premise. A genuine radius-times-unit-vector representation, including x=0, and actual polynomial homogeneity prove |P_li(x)|<=B^l K_l for norm(x)<=B, B>=0.

The actual tensor grid lies in the radius-2 ball. Substituting the derived values into genuine finite tensor interpolation proves the actual coefficient envelope

    coefficientNorm(P_li) <= E_l = 2^l K_l (4^l exp(l+1))^3.

The compact derivative bound is consequently the actual all-order inequality

    jetNorm(P_li,N,b) <= (N+1) E_l (2^N)^2 (2^N max(1,b))^l.

The final wave estimate substitutes this derived normalization into the actual entire solid-wave spatial Frechet derivative estimate, on genuine compact balls including origin. No coefficient, derivative or convergence conclusion is assumed. An additional derived bound K_l<=(1+angularArea^(-1))(l+1)^3 makes the envelope explicitly polynomial times exponential in degree, sufficient against the already proved factorial radial majorants. The constants depend on compact radius/order/frequency and actual fixed sphere area; not on degree, stack or large physical radius.

This file does not assert cross-degree orthogonality, a global Hilbert basis, or spatial Green/Maxwell series convergence. The actual k=0 annular moment argument is the authorized next cross-degree step.

Status: author PASS and root complete-source plus independent pinned compiler PASS; no warnings and all selected dependency reports standard-only. Frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 9 reports use only standard foundations. Final source SHA256 `c1151e2d425429397a7ddfa169e12778a73259005e6b35e24230cf2539c79dde`. Independent log `lean/logs/NormalizedHarmonicJets-root-audit.log`, SHA256 `ff0a4b4be962173a3c48f0002b922152d481461a45391d2bc259dd3311850c70`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
