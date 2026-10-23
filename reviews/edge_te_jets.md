# Literal TE edge-jet map

Frozen source: lean/EdgeTEJets.lean.
SHA256: 42266D5FE7C310F3C69D8CCDFB6C9B9BBD334DFFF53B228EFEC6FBEB28A6FEA5.
Author final pinned compiler/object PASS: exit 0, no warnings, two standard-only reports. Log: lean/logs/EdgeTEJets-final.log. Independent audit pending.

The literal Debye TE fields at (r,y,0) satisfy the actual electric Ez and magnetic Hx/Hy formulas in terms of scalar planar two-jets; mixed partial commutation and the Helmholtz equation are used with their actual Frechet definitions. An explicit six-component target jet has a right inverse onto arbitrary prescribed (Ez,Hx,Hy) for k and r nonzero. The scalar Helmholtz equation is the generic input here; RestrictedTEFields derives it for the actual finite harmonic sums. No vector-jet surjectivity conclusion is assumed.
