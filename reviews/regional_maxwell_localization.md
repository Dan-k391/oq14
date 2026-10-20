# RegionalMaxwellLocalization — actual material-weight localization

Source: `lean/RegionalMaxwellLocalization.lean`

SHA256: `74EC5841F2BE6CCA1A4915EEEA19BAE7EF02CE3FC20F3A53197C81DA6587289F`

Evidence: `lean/logs/regional-maxwell-localization-check.log`. Final compile
exited zero without warnings, created an importable object (198592 bytes),
and emitted ten selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

Every literal compact C-infinity regional test becomes an actual compact
Schwartz test using the existing FourierL2.compactSmoothSchwartz
constructor. Its actual coordinate derivative agrees with the regional
partial test, so both global Maxwell curl pairings agree exactly with
the new regional pairings. No distribution-test class equivalence is
assumed.

If the actual material-weighted electric field epsilon(x) E(x) equals
epsilon0 E(x) almost everywhere on the region, multiplication by a
regional test gives the same integral everywhere: outside the region the
test vanishes pointwise. The actual global MaterialMaxwell.TestMaxwell
equations therefore supply constant-epsilon0 regional Maxwell equations.
No material derivative, coefficient continuity, interface regularity,
trace, or boundary term is required.

The contrast-zero helper derives that weight equality from
(epsilon(x)-epsilon0) E(x)=0 almost everywhere on the region. A separate
material-or-zero helper handles the actual interface mechanism:
epsilon(x)=epsilon0 or every electric component vanishes at x. These are
explicit physical hypotheses; the field is never assumed to solve local
Helmholtz.

The final E/H exports combine the derived regional Maxwell equations with
the audited actual Maxwell-to-Helmholtz theorem. With positive epsilon0,
nonzero real k, and actual globally locally integrable components, they
prove the exact WeakHelmholtzRegularity.IsWeakHelmholtz predicate at
frequency k sqrt(epsilon0). The transfer does not claim any smooth
representative or unique continuation by itself.

Self-review checked compact-to-Schwartz conversion, derivative agreement,
actual weak curl signs, AE weight equality only inside the test support,
pointwise vanishing outside the region, complex contrast embedding,
constant factor extraction, and reuse of actual local integrability.

Root independently read the complete final source and independently
recompiled all ten exports at the recorded hash. Source frozen.
