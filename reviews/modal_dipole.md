# Actual complex-frequency dipole Maxwell fields

Source: `lean/ModalDipole.lean`; namespace `OQ14.ModalDipole`.

This module constructs actual three-dimensional fields and proves their actual Frechet-coordinate curl equations. It uses the same Euclidean space and curl operator as the frozen Maxwell calculus; the complex frequency is allowed because resonance fields require it.

For differentiable scalar radial coefficients, the code first proves the curls of `A(r)e_z+B(r)x_z x` and `C(r)(x cross e_z)` by coordinate product and chain rules. All coordinate derivatives and the derivative of the Euclidean norm are actual derivatives. The final component of the magnetic curl uses the proved Euclidean coordinate-square identity.

For a radial Riccati solution u, the constructed fields are

`E=(u'/r)e_z+(2u/r^4-u'/r^3)x_z x`,

`H=(i*kappa^2/k)(u/r^2)(x cross e_z)`.

Actual derivatives of all radial coefficients are proved. The scalar relation `u''=(2/r^2-kappa^2)u`, together with `kappa^2=k^2*epsilon` and k nonzero, gives `curl E=i*k*H` and `curl H=-i*k*epsilon*E`. The generic theorem takes the radial ODE as a hypothesis, but does not take either Maxwell equation as a hypothesis.

The final two theorems discharge that radial ODE for the actual degree-one regular and outgoing Riccati functions. Their real-radius derivatives are obtained from the already verified complex derivatives using restriction of scalars in the chain rule. Thus the actual fields built from psi(1,kappa*r) and xi(1,kappa*r) satisfy the complex-frequency Maxwell equations on punctured Euclidean three-space. No determinant or matching premise is required.

The regular field is not yet extended at the origin in this module. Although its singularity is removable in the mathematical construction, this formal source only claims the punctured-space result it proves. Interface-trace equivalence, origin regularity, and full outgoing operator identification remain separate formal obligations. The outgoing field uses the actual outgoing exponential in the Riccati definition; no decay assertion is made for a complex resonance frequency.

Self-audit checked the sign of x cross e_z, the two curl identities, all real-radius chain rules, the electric and magnetic normalizations, the factor kappa^2/k, and the actual degree-one ODE instantiations. All 14 fully qualified exports compile with only standard axioms and no proof placeholders. Evidence: `lean/logs/modal-dipole-check.log`.
