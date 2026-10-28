# ModalDipoleOrigin — independent root audit

PASS, 2026-10-27. Full source and mathematical scope reviewed independently. Fresh pinned Lean 4.19.0 source compilation completed with exit 0. Source SHA256: `A944E56CFDD8EF20B5B9BA243F174034098AC332177DBA52FF8C8BAFA4876885`.

Audit log: `lean/logs/ModalDipoleOrigin-root-audit.log`, SHA256 `9D5E62A2D7419CF819CA9CD3CA95B6EE0D05E4999D4B4FDD128D5E43B61AC6BC`. Exit receipt: `lean/logs/ModalDipoleOrigin-root-audit.exit.log` = 0. All 16 selected reports use only `propext`, `Classical.choice`, and `Quot.sound`; no warnings, errors, or proof placeholders. The fresh check re-elaborated this source against existing dependency objects; it was not a clean dependency rebuild.

The regularized determinant retains the exponential prefactor and equals the actual degree-one matching determinant for nonzero n and z. Its value at z=0 is I n(n²+2)/3. Joint continuity and the exact value I at n=1 yield uniform zero exclusion on every compact frequency set. The actual nonzero determinant roots therefore escape every bounded frequency disk as real n tends to 1. The argument includes the previously missing approach to the origin and does not use the invalid ratio estimate there.

The arbitrary-filter escape theorem assumes actual determinant zeros, as appropriate for a statement about roots. It does not select roots or prove all-degree noncoincidence, polynomial-branch nonidentity, or any volume-kernel or resolvent claim. Those limitations agree with the author receipt.
