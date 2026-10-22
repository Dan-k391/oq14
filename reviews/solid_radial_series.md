# Actual entire normalized regular radial factor in squared radius

Source: `lean/SolidRadialSeries.lean`.
SHA256: `FE32381F6974315CBA174B7C1B238B22237931066C5159BEF3BD2F334E31F38B`.

Author final compiler exit 0, no warnings; importable object 506584 bytes. All twenty-one selected reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/SolidRadialSeries-final.log`.

F_l(t) is the literal power series sum of the actual signed Riccati coefficients times t^m. F1 and F2 are literal once- and twice-shifted coefficient series. The actual factorial majorants and amplitude recurrence establish summability and actual first and second derivative identities. F and F1 are proved entire and globally smooth, including t=0.

The actual coefficient recurrence proves

    4t F2_l(t)+(4l+6) F1_l(t)+F_l(t)=0

for every complex t. The proof uses genuine summable series algebra, its zero leading coefficient, and actual coefficient reindexing. No ODE or derivative identity is assumed. The same equation is exported with genuine `deriv` expressions.

Actual termwise algebra identifies origin_l(z)=z^(l+1)*F_l(z^2) at every complex z. F_l(0)=A_l, the actual positive regular origin coefficient. Away from zero, F_l(z^2)=psi_l(z)/z^(l+1); actual regular values on the positive real axis have the corresponding exact factorization. These away-from-zero formulas do not supply a value by division at zero.

Both F and F1 have the explicit genuine bound norm(F_l(t)),norm(F1_l(t))<=A_l*exp(norm(t)/2). This squared-radius factor permits smooth solid-harmonic scalar waves at the spatial origin. The spatial Helmholtz construction is a separate successor.

Status: author PASS and root complete-source / independent pinned compiler PASS. Source frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 21 reports use only standard foundations. Final source SHA256 `fe32381f6974315cba174b7c1b238b22237931066c5159bef3bd2f334e31f38b`. Independent log `lean/logs/SolidRadialSeries-root-audit.log`, SHA256 `56a5d368ae52de798332c872c145b3fdd4a921b6b6fc2918d396045db1068aa5`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
