# Actual entire Riccati extension and all-order compact derivative bounds

Source: `lean/RiccatiCompactDerivatives.lean`.
SHA256: `7FCBB27314530CF8D8E0CFA853F69C5551CA196972C70EED167C62179DE6832A`.

Author final compiler exit 0, no warnings; importable object 299072 bytes. All nine selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RiccatiCompactDerivatives-final.log`. The pinned missing Liouville dependency was built successfully without changing any dependency version; log `lean/logs/Liouville-target-dependency.log`.

The actual proved origin series is entire. Its existing term estimates and the genuine exponential series give norm(origin_l(z))<=A_l*b^(l+1)*exp(b^2/2) throughout the complex disk of radius b, including zero.

A generic genuine Cauchy argument proves that, for an entire smooth scalar complex function bounded by M on that disk, its nth derivative is bounded by M wherever norm(z)+n<=b. The induction applies the actual first derivative Cauchy estimate on unit circles, using the previous derivative's genuine differentiability and the triangle inequality. No derivative bound is a premise.

For the actual Riccati function this yields the same explicit amplitude bound for every fixed derivative order, with a larger fixed disk chosen as a function of order and source compact. Actual local equality with psi identifies every complex derivative away from zero. Actual real restriction and local equality identify every real derivative of the finite regular function at positive radii.

The proved Gaussian lower bound gives A_l*b^(l+1)<=exp(b^2/2)*regular(l,b) in the actual barrier. Consequently

    norm(D^n origin_l(z)) <= exp(b^2)*regular(l,b)
    whenever norm(z)+n<=b and b^2<l(l+1), b>0.

The radius b is fixed independently of degree, shell radius and stack. These bounds genuinely include the analytic origin extension. They do not equate the raw finite psi value at zero with the extension, nor identify a spatial Maxwell dyadic expansion.

Status: author PASS and root complete-source mathematical audit plus independent pinned compiler PASS, exact frozen hash; no warnings and all nine reports standard-only. Root log: `lean/logs/RiccatiCompactDerivatives-root-audit-final.log`. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 9 reports using only standard foundations. Final source SHA256 `7fcbb27314530cf8d8e0cfa853f69c5551ca196972c70eed167c62179de6832a`. Independent log: `lean/logs/RiccatiCompactDerivatives-root-audit-final.log`; log SHA256 `bb66cc08eecf52c538acf43b87941bbbabbfcd3001c218ec14b119d132ecbd33`. This certifies the stated scope, not either complete OQ14 construction.
