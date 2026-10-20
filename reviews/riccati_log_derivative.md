# Actual regular logarithmic derivative in the barrier

Source: `lean/RiccatiLogDerivative.lean`.

SHA256: `19E233DF3846C1C511CE98543DD2D3D57247F2E6DA97C16CB258F75EC640F3D3`.

Final author compiler exit 0; importable object 522296 bytes; all nine selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output: `lean/logs/riccati-log-derivative-check.log`.

For the actual entire regular extension, the derivative of the literal weighted expression x^(beta-1)(x u'-beta u) is proved directly from the actual second-order ODE. The expression is continuous at zero and vanishes there. The previously proved actual barrier positivity determines its derivative sign, so genuine monotonicity supplies lower and upper comparison values without any Riccati comparison hypothesis.

The explicit manuscript root gamma=(1+sqrt(1+4(l(l+1)-R²)))/2 is proved at least one, at most l+1, and to satisfy gamma(gamma-1)=l(l+1)-R². Consequently the actual real regular Riccati logarithmic derivative satisfies gamma≤x regularD(l,x)/regular(l,x)≤l+1 on 0<x≤R whenever R>0 and R²<l(l+1).

All positivity, normalization, derivatives and endpoint data are proved from the identified series and actual finite Riccati functions. No expansion or scalar comparison conclusion is assumed. The sharper Gaussian lower amplitude estimate is a separate next step.

Status: root independent full-source audit and compiler PASS, with standard-only reports and no warnings. Frozen unchanged at the hash above.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 9 reports use standard foundations. Final source SHA256 `19e233df3846c1c511ce98543dd2d3d57247f2e6da97c16cb258f75ec640f3d3`. Independent log: `lean/logs/RiccatiLogDerivative-root-audit.log`. The remaining complete Maxwell constructions are outside this audit.
