# Actual common-stack high-degree geometry and tail decay

Source: `lean/RadialStackHighTail.lean`.

SHA256: `1BACE4B17B0D2C4A8E59210F478A1CD87609FD9433235C9C79145CA701F409A2`.

Author final compiler exit 0, no warnings; importable object 205424 bytes. All nine selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialStackHighTail-final.log`.

Induction on the actual shared-radius `RadialStack.Chain` proves that every layer outer radius b_g is at most the actual outer radius X. With q>=1, q_g<=q, X<=2R and l>=2qR, positivity of actual layer radii gives q_g*b_g<=l. Squaring yields q_g^2*b_g^2<=l(l+1), the actual stack barrier. No connectivity, barrier, load sign, or tail conclusion is substituted as an assumption.

The remaining exports specialize the actual reaction bound and weighted tail summability, explicit sum envelope, superalgebraic decay and zero limit to genuine Chain families and the stated common material/radius bounds. The cutoff is 2qR; it implies l>=2R and the elementary window coverage lemma records that every degree belongs to the complementary intermediate window or the high window, including the shared boundary.

The estimates concern actual scalar radial source coefficients. Spatial Maxwell Green reconstruction, vector angular expansion and full physical all-order convergence are not claimed.

Status: author PASS and root full-source mathematical audit plus independent pinned compiler PASS (session 44460), exact hash unchanged; no warnings and all nine reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 9 reports using only standard foundations. Final source SHA256 `1bace4b17b0d2c4a8e59210f478a1cd87609fd9433235c9c79145ca701f409a2`. Independent log: `lean/logs/RadialStackHighTail-root-audit.log`; log SHA256 `ab0c837b907083ca1598b7995ec3492f66072885d9bbef415580f35e0d3d99aa`. This certifies the stated scope, not either complete OQ14 construction.
