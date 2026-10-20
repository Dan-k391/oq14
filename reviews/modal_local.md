# ModalLocal scope and self-audit

The module proves actual local square integrability of the unchanged assembled spherical electric, magnetic, and displacement fields. Its 12 exports prove the stronger statement of MemLp membership at every exponent on every compact or bounded region. Only nonzero frequency is needed for these regularity results; interface matching is not a premise.

The basic construction expresses each radial piecewise profile times a continuous coordinate polynomial as a measurable piecewise combination of two globally continuous functions. The exterior profile is evaluated at max(radius, 1/2) only in this auxiliary representation. Where the exterior field is actually used, radius exceeds one, so this clipping is exactly equal to the original profile. The interior profiles are entire at the origin. Continuous functions are bounded on each compact region, and its finite volume supplies the actual Lp estimate. Indicator sums handle both the sphere jump and the material multiplication.

The final bounded-region results restrict the compact-ball estimates. They do not require global square integrability of an outgoing field at complex frequency. The next graph-space assembly can therefore use genuine local L2 data and the already proved global compact-test Maxwell identities.

Self-audit checked the clipped-profile equality, measurability at the sphere, normal electric jump, the exterior B-profile derivative, coordinate factors, negative magnetic component, and the restriction direction for bounded sets. No regularity or H(curl) membership is assumed.

Evidence: `lean/logs/modal-local-check.log`, successful compiler exit with 12 standard-only axiom reports. Source SHA256: `CB87B90D94BFCB3F9970AC31D5C0C31CE59E8B4D8F8AF54C9C4FCD9148FD1465`.

The channels agent independently read all 12 exports and passed the audit: exact clipped representation, all-exponent compact bounds, indicator jumps, bounded-set restriction, and the nonzero-frequency hypothesis all check.
