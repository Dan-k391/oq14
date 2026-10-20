# Conical angular trial

Author verification for `lean/ConicalAngularTrial.lean`.

- Source SHA256: `4A18DADF8555EF04E6C00979D586F407E63FC485E4CE93FFE7C45E0AFD726D73`.
- Pinned Lean 4.19.0, `lake env lean -o .lake/build/lib/lean/ConicalAngularTrial.olean ConicalAngularTrial.lean`: exit 0; object emitted, 502800 bytes.
- Exact log `lean/ConicalAngularTrial.final.log`, SHA256 `0A10F16B778B00E4BB08D8397AEF5E952C16D62C6BF74F006352036AD7AF3CE7`.
- All twenty-three theorem dependency reports contain only `propext`, `Classical.choice`, `Quot.sound`; no compiler warnings.

For the actual sphere and its actual angular measure, define the coordinate `z(n)=n(2)`, the cap `|z|>t`, and `q=1+d*1_cap`. Coordinate permutations preserve the actual angular measure, hence the three coordinate-square integrals agree and the unweighted integral of `1-3z^2` vanishes. Actual negation preserves the cap and proves the weighted mean of `z` is zero.

The tangent vector is `e_i-n(i)n`; the source proves tangency, its norm squared `1-n(i)^2`, and its inner product with each tangent direction equals the actual ambient coordinate Frechet derivative in that direction. Thus the trial energy uses the actual coordinate derivative on tangent directions. It is not a separately specified energy surrogate.

The cap is nonempty open for `t<1`, with an explicit pole witness; the actual angular measure is positive on it. If `t>=0` and `3*t^2>1`, the cap integrand `1-3z^2` is strictly negative there. Its integral is strictly negative by the actual support/integrability criterion. The weighted denominator is positive using actual full support and the coordinate pole. The exact integral balance then gives the strict quotient bound for `d>0` and `1/sqrt(3)<t<1`.

Scope: this proves the actual variational trial and its strict estimate. It does not establish a sphere Sobolev space, compact embedding, Poincare inequality, eigenvalue attainment, or a weighted angular eigenfunction. The manuscript's eigenfunction-existence step remains open.

Independent root full-source mathematical audit and pinned compiler recheck PASS at the exact source hash above, all twenty-three standard-only reports. Source frozen.
