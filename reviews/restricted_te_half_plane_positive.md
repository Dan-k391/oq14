# Positivity of the half-plane profile integral

Author final pinned compiler/object PASS: 4 reports (U_isOpen, U_nonempty, psi_pos_on, halfPlane_pos), each standard-only [propext, Classical.choice, Quot.sound]; exit 0, no warnings, no errors. Frozen source: lean/RestrictedTEHalfPlanePositive.lean, SHA256 4d1d324f8e8047f1d0d7fde90c4ead61005990dfb66d49a3d226939ba3f1bc97. Final log: lean/logs/RestrictedTEHalfPlanePositive-final.log, SHA256 03aba3f29c8ad58908a47e606d5e173403113bb8354dec5174196b9726b20c68 (exit file lean/logs/RestrictedTEHalfPlanePositive-final.exit.log, value 0). Imports the frozen RestrictedTEDipoleProfile object. Root independent audit pending. Frozen source.

Proved: for a unit plane vector n and a positive height h, `0 < halfPlane n h`: the tangential profile `psi n h` is strictly positive on the open half plane `U n`, hence the integral of its indicator is strictly positive (`integral_pos_iff_support_of_nonneg` with the open nonempty set `U n` of positive measure). Together with the finiteness already proved this makes the explicit constant `p0 = Vb rho * halfPlane n h / scale` of `RestrictedTEConcreteDevice.concrete_counting` strictly positive, so positive thresholds `0 < ηt < p0` are meaningful.

Not proved: the value 1/(2 pi h).
