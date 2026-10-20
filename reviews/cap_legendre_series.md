# Cap Legendre series

Author verification for `lean/CapLegendreSeries.lean`.

- Source SHA256: `C41E23355D89894F10566D2A4B70203D552AC0F420B2A2ADF23551DEF7FCCFAE`.
- Pinned Lean 4.19.0 `lake env lean -o .lake/build/lib/lean/CapLegendreSeries.olean CapLegendreSeries.lean`: exit 0, no warnings; object 1528640 bytes.
- Exact log: `lean/CapLegendreSeries.final.log`, SHA256 `5ACB08E31B98773780A6B10118B05E52AAFC7DDC5B4BF0391D533488ABC74B98`.
- All forty-five theorem dependency reports contain only `propext`, `Classical.choice`, `Quot.sound`.

The two coefficient recurrences are actual recursively defined real sequences. On the actual parameter interval `[0,2]`, the pole coefficients have absolute value at most two and the odd coefficients lie in `[0,1]`. Hence the real series genuinely converge on their stated spatial domains. Differentiation is proved from polynomial coefficient-growth bounds and a summable uniform bound on the actual derivatives. First and second moment identities justify summing the coefficient recurrence; this yields the literal Legendre equation for the actual sums, rather than a formal equation supplied as a premise.

The source proves actual first and second derivatives for the regular-pole series in `(1-z)/2` and the odd series `z*Y(z^2)`. Parameter continuity of the sums and derivative sums follows from actual uniform summable majorants on `[0,2]`. Exact endpoint recurrences give `P_0=1`, `P'_0=0`, `P_2=F_2=z`, `P'_2=F'_2=1`. Nonnegative odd coefficients imply `F_a(z)>0` for `0<z<1` and `F'_a(z)>=1` for `|z|<1`. The pole normalization `P_a(1)=1` holds literally.

Independent root full-source and compiler audits requested. Source held stable. Scope: actual one-dimensional solutions and parameter control; no matching root, spherical weak eigenfunction, sphere Sobolev compactness, or eigenvalue attainment is asserted in this module.

## Independent root verification on resumption

Full source reviewed and pinned Lean compiler returned exit0. All 45 selected reports use only the standard foundations. Source SHA256 `c41e23355d89894f10566d2a4b70203d552ac0f420b2a2adf23551def7fccfae`. Independent log: `lean/logs/CapLegendreSeries-independent-root.log`. Actual definitions and hypotheses were checked; this result does not close the outstanding full Maxwell/OQ14 constructions.
