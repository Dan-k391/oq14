# MaxwellZeroField — actual electric AE zero implies magnetic AE zero

Source: `lean/MaxwellZeroField.lean`

SHA256: `D2A37B7AF62CEBB4332C968FD7F2D44165C2AF0F74F47C79A13D68CF0F677898`

Evidence: `lean/logs/maxwell-zero-field-check.log`. Final compile exited
zero without warnings, created an importable object (113504 bytes), and
emitted five selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

Actual global electric AE zero makes every literal electric test integral
zero, hence makes its weak curl pairing zero. The actual first global
MaterialMaxwell.TestMaxwell equation and nonzero real frequency imply
that every actual magnetic compact Schwartz test pairing vanishes.

For each actual component and every real compact C-infinity scalar test,
the real test is embedded into the complex numbers and converted into
an actual compact Schwartz test by FourierL2.compactSmoothSchwartz.
Its pairing is exactly the one already proved zero. The pinned actual
fundamental lemma for locally integrable functions therefore proves the
magnetic component zero almost everywhere. Combining the three finite
components gives actual vector-field magnetic AE zero.

The final hypotheses are the actual global MaterialMaxwell.TestMaxwell
equations, nonzero real k, actual global component local integrability of
H, and literal E=AE0. Permittivity may vary arbitrarily: this consequence
uses only the first curl equation. There is no extra distributional
separation premise, magnetic zero assumption, field differentiability,
or assumed scalar Helmholtz equation.

Self-review checked whole-field AE evaluation into components, exact
weak curl signs, nonzero I k division, real-test complex embedding,
compact-to-Schwartz conversion, use of the actual fundamental lemma,
and reconstruction of the vector-field AE statement.

Source frozen pending root independent mathematical audit.
