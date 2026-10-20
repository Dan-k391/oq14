# ModalProfiles scope and self-audit

The module instantiates the spherical interface calculus with the actual electric and magnetic profiles from the factorial-series Riccati functions and the entire regular-center extension. Its 34 exports include genuine profile regularity, actual derivatives, exact matching, the continuous-potential decomposition and the assembled classical Maxwell equations off the interface.

The potential is `P_in=−(a/n)(nk)^2 profile(nkr)` and `P_out=−b ξ₁(kr)/r²` plus an explicit constant. The constant makes the two potential values equal at radius one. It changes neither gradient nor Maxwell field. Both actual derivative identities `P′=rB` are proved. The normalization of the interior electric tangential coefficient is `k ψ₁′(nk)a`; the magnetic coefficient is `ik n ψ₁(nk)a`. Thus the actual matching matrix implies continuity of A, C, and Q=A−P at the sphere.

The assembled electric field is precisely the previously constructed regular interior and outgoing exterior, with no field replacement. Away from the origin it equals the actual weak potential gradient plus the axial field Q e_z. The potential gradient is locally integrable and its weak curl is zero against every compact C2 scalar test, derived by the prior actual radial weak derivative theorem. The axial field and the magnetic field are continuous. The assembled classical Maxwell equations use the actual piecewise dielectric coefficient and hold at every point off the sphere, including the origin.

Self-audit checked the potential derivative signs, the interior a/n normalization, exterior k cancellation, the matching order, and both componentwise field identities. The additive exterior potential constant only serves continuity. The full assembled weak Maxwell conclusion is the next module; it is not asserted here as a premise or as a completed result.

Evidence: `lean/logs/modal-profiles-check.log`, 34 standard-axiom reports after a successful compiler invocation.
