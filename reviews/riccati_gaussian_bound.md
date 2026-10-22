# Actual Gaussian barrier amplitude bounds

Source: `lean/RiccatiGaussianBound.lean`.

SHA256: `42322EE69836FAD2FA012B816630ED047082CA029319A45376E677CDA2826BE4`.

Final author compiler exit 0; importable object 709056 bytes; all 15 selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/riccati-gaussian-bound-check.log`.

Put m=l+1, gamma=(1+sqrt(1+4(l(l+1)-R²)))/2, p=l+gamma and d=p+2. The actual continuous normalized logarithmic derivative y satisfies its proved Riccati equation and gamma≤y≤m. Direct differentiation proves that the literal deficit G=x^p(m-y-x²/d) has derivative (x^p/x)(gamma-y)(m-y)≤0. Its actual origin value is zero, so m-y≤x²/d.

The actual normalized regular function v=u/x^m has derivative v(y-m)/x. Therefore exp(x²/(2d))v is monotone increasing on the closed barrier interval, using the just-derived deficit estimate. Its actual origin value is the identified coefficient A_l. This yields the Gaussian lower bound. Separately, y≤m makes v monotone decreasing and yields the companion upper bound.

Factorial algebra identifies A_l exactly with 1/(2l+1)!!. The final actual two-sided theorem, for every 0<x≤R with R>0 and R²<l(l+1), is

    x^(l+1)/(2l+1)!! * exp(-x²/(2(l+gamma+2)))
      ≤ regular(l,x) ≤ x^(l+1)/(2l+1)!!.

This is the manuscript normalization and estimate, with the actual finite Riccati regular function. No series identification, positivity, Riccati comparison, endpoint value, integral identity or Gaussian bound is assumed. The proof uses genuine derivative signs and closed-interval monotonicity throughout.

Status: author compiler PASS; ready for root independent full-source audit and compiler. Source held unchanged pending audit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 15 reports using only standard foundations. Final source SHA256 `42322ee69836fad2fa012b816630ed047082ca029319a45376e677cda2826be4`. Independent log: `lean/logs/RiccatiGaussianBound-root-audit.log`; log SHA256 `2c246d83dff49f61d15ed71516c8a6f350612c728f43135066115c643296ea0d`. This certifies the stated scope, not either complete OQ14 construction.
