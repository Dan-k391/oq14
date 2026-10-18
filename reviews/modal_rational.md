# Exact finite polynomial obstructions for spherical TM poles

Source: `lean/ModalRational.lean`; namespace `OQ14.ModalRational`.
This imports the frozen factorial-series and Wronskian modules.

The module defines actual `Polynomial ℂ` objects Q, A and B. Their evaluated functions are proved equal to the existing finite factorial inverse polynomial and to Cplus(1/w), Cminus(1/w) away from zero, respectively. Polynomial formal derivatives are tied to actual complex derivatives by the checked polynomial derivative API and derivative uniqueness.

For a hypothetical multiple pole z, with n,z nonzero, the actual determinant and actual derivative zero conditions imply

`M(1/z)=0`, where `M(w)=w²(B'(w)A(w)−B(w)A'(w))+2inB(w)A(w)`.

The exact value at zero is `2in B(0) A(0)`. It is nonzero when n is outside 0,+1,−1. Thus M is a nonzero polynomial, and every fixed degree has only finitely many nonzero multiple determinant zeros. This is unconditional over complex n subject to those exclusions; it does not use an algebraicity or transcendence hypothesis.

For distinct degrees l,j, every common nonzero determinant zero is a root, in inverse coordinates, of `A_l B_j−A_j B_l`. The module proves this separation polynomial is nonzero from its first two exact coefficients. If its constant coefficient were zero, the derivative at zero reduces to a nonzero factor times `l(l+1)−j(j+1)`. The latter is nonzero for different natural degrees. Consequently each fixed distinct pair of degrees has only finitely many common nonzero zeros.

The first derivative identities are derived from the actual factorial coefficient recurrence and evaluated polynomial derivatives. They are not assumed asymptotic coefficients. The nonzero-polynomial arguments and finite-root-set deductions use ordinary polynomial APIs. Inversion maps the finite inverse-coordinate root set to a finite set in the physical z coordinate.

Self-audit: quotient derivatives are used only after the general Wronskian theorem proves Cplus nonzero at a pole. All inverse-coordinate derivative steps enforce z≠0 and n≠0. The n≠±1 conditions are introduced precisely where the constant matching coefficients must be nonzero. Finite common-zero sets for each pair do not imply that a pole avoids the countable union over all other degrees; no such conclusion is claimed. Likewise finite multiple-zero sets need not be empty.

Remaining formal work includes algebraicity of these roots for algebraic n; the full Lindemann-Weierstrass transcendence theorem; existence and isolation of the desired operator pole; and the continuum Maxwell device result. The cached mathlib version contains only the analytic part of Lindemann-Weierstrass, not the full exponential transcendence theorem. A genericity replacement would need an actual proof and cannot be inferred merely from countability.

All 17 exported theorems are compiled with fully qualified axiom reports. Only standard `propext`, `Classical.choice`, and `Quot.sound` appear. No `sorry`, `admit`, or new axiom is used. Evidence: `lean/logs/modal-rational-check.log`.
