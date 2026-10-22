# Actual global regular solid-harmonic Helmholtz waves

Source: `lean/SolidScalarHelmholtz.lean`.
SHA256: `36C7E4A685FC23D06359DD86902E06420111BA192B1066BBD1B4FF424BD55D82`.

Author final compiler exit 0, no warnings; importable object 262536 bytes. All ten selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/SolidScalarHelmholtz-final.log`.

For an actual real formal harmonic homogeneous polynomial P of degree l, the source defines the actual wave

    F_l(q^2*norm(x)^2) * complexEvaluate(P,x).

The actual entire squared-radius factor makes this wave globally smooth over real three-space, including the origin. Genuine first and second derivative calculations in squared radius transfer the proved normalized F ODE to the actual radial ODE. The existing global norm-squared harmonic Laplacian formula, together with the actual polynomial Laplacian and Euler identities, proves Delta(wave)+q^2*wave=0 at every spatial point. There is no puncture, PDE extension assumption, or missing origin case.

The exact origin value and a genuine coefficient-based norm bound are exported. Away from zero and for q nonzero, the wave is identified exactly with psi_l(q*r)/(q*r)^(l+1) times the actual solid harmonic polynomial. This records the normalization needed to compare with punctured spherical waves; no value is supplied by division at zero.

This is an actual global scalar Helmholtz construction. The harmonic polynomial may be zero; nonzero vector Maxwell polarization is not asserted here. Debye/vector reconstruction remains the root task.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 10 reports use only standard foundations. Final source SHA256 `36c7e4a685fc23d06359dd86902e06420111ba192b1066bbd1b4ff424bd55d82`. Independent log `lean/logs/SolidScalarHelmholtz-root-audit.log`, SHA256 `c6a6b70c10aa5639c1274c116d5eac999efa38fefe15338b1b4646739fcd036c`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
