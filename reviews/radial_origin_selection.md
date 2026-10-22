# Genuine regular radial selection at the origin

Source: `lean/RadialOriginSelection.lean`.
SHA256: `7F94CBAC8A50B6CF2DDD09157AB0BE113F16FA441D1836E20B9A219E6FEB0E57`.

Author target plus importable object compiler exit 0, no warnings. Object 414912 bytes. Nine selected dependency reports standard-only. Log: `lean/logs/RadialOriginSelection-final.log`. Forbidden-token scan passed.

The regular function is the actual entire origin series at k*r, with derivative k*originD(k*r). Actual series facts give genuine origin continuity of both functions, zero regular value at zero, exact equality with the half-sum of the literal outgoing and incoming Hankel functions away from zero, actual derivative equations and actual regular/outgoing Wronskian I*k.

For a genuine second-order radial solution on (0,L), with actual first/second derivative equations, actual f and df continuous at zero and f(0)=0, variation coefficients derive its literal regular/outgoing basis expansion. The actual Wronskian of f with the regular solution has zero derivative on the connected interval, and continuity at the actual closure endpoint zero forces its value to zero throughout. Differentiating the derived expansion at an actual interior point and using the nonzero actual Wronskian forces the singular coefficient to vanish. Thus the actual regular expansion is a conclusion, without an assumed expansion or singular asymptotic premise. The explicit ODE/origin premises are discharged for the actual Green kernel separately.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 9 reports use only standard foundations. Final source SHA256 `7f94cbac8a50b6cf2ddd09157ab0be113f16fa441d1836e20b9a219e6feb0e57`. Independent log `lean/logs/RadialOriginSelection-root-audit.log`, SHA256 `3a953f5c41a478b0f7ddca1bfa2e1691e0c1b469220b9738d92717d2e5e7d8d0`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
