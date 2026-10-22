# Explicit physical-to-reduced scalar Green sign

Source: `lean/ScalarGreenReduced.lean`.
SHA256: `497CA325E6BBAD66FDD497EB636EF869DA937D49971FAE8EF3D08BE3218CDF47`.

Author target and importable object EXIT0, no warnings; 200608 bytes. Three selected reports standard-only. Log `lean/logs/ScalarGreenReduced-final.log`. Forbidden-token scan passed.

Literal reducedFree is psi(min)*(chi(max)-I*psi(max)) using the actual real Hankel basis. The actual entire regular function and outgoing xi identify this with -I*origin(min)*xi(max). The previously derived physical Green moment formula thus equals minus P(y)*reducedFree(k*r,k*s)/(k*s^l*r*s), with s=norm(y). All divisions have genuine positive/nonzero hypotheses. This derives the minus sign and 1/k scaling rather than absorbing either into a convention. It agrees with manuscript radial_green_limit.tex reduced radial derivative-jump +1 and physical outgoing Phi convention. Electric dyadic k^3 normalization remains a separate differential reconstruction claim.

Status: author PASS; frozen pending root full-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `497ca325e6bbad66fdd497eb636ef869da937d49971fae8ef3d08be3218cdf47`. Independent log `lean/logs/ScalarGreenReduced-root-audit.log`, SHA256 `a0b4210a9ff256117938e67069998a39b4cc4a5abb7b5f93d398415df04ce832`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
