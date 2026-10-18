# Actual existence and fixed-degree simplicity of spherical TM zeros

Source: `lean/ModalExistence.lean`; namespace `OQ14.ModalExistence`.

This module proves existence of zeros of the actual factorial-series TM determinant. It introduces no resonance-existence premise. The proof uses a genuine inverse-coordinate contraction on a closed complex ball, constructed from a local logarithmic correction to an actual polynomial quotient.

For a locally Lipschitz correction H with H(0)=0, the first theorem constructs a fixed point of w ↦ 1/(z₀+H(w)). Explicit bounds prove that this map preserves the ball and is a contraction with constant 1/2 when |z₀| is sufficiently large. The fixed point is nonzero, so its inverse solves z=z₀+H(1/z). Completeness and existence come from mathlib's proved contraction theorem.

For actual polynomials A and B nonzero at zero, the code constructs H(w)=a⁻¹ log((-B(w)/A(w))/(-B(0)/A(0))). Polynomial differentiability and the actual logarithm near 1 give local Lipschitz control and nonvanishing neighborhoods. Exponentiating the fixed-point equation proves exp(a z)=-B(1/z)/A(1/z). Actual complex exponential periodicity supplies constant-quotient roots of arbitrarily large modulus; the bounded displacement supplied by the contraction then proves unbounded roots of the polynomial-quotient equation.

The final theorems instantiate the actual matching polynomials and determinant factorization from the preceding modules. For every natural degree and every complex refractive index n outside 0,+1,−1, there are nonzero determinant zeros of arbitrarily large modulus. The previously proved finite set of multiple zeros then yields simple zeros of arbitrarily large modulus. These zeros can also avoid any prescribed finite set of complex points.

This bypasses the full Lindemann–Weierstrass step for existence and eventual simplicity within one fixed degree. It does not prove that one zero avoids every other angular degree: a countable union of pairwise finite overlap sets cannot be discarded by the finite-exception argument. It also does not identify operator poles or their multiplicity, prove a lower-half-plane or high-Q asymptotic, or discharge the manuscript's full spectral and Maxwell analytic chain. Those remain separate formal obligations. No root-location or operator conclusion is hidden in the term “TM zero.”

Self-audit checked the inverse-map nonvanishing, the contraction denominator estimate, the closed-ball completeness premise, the logarithm's local branch and exponential recovery, actual periodic roots, polynomial evaluation at the inverse coordinate, and the finite-exception bound. All eight fully qualified exported theorems compile and report only standard Lean axioms. Evidence: `lean/logs/modal-existence-check.log`.

Independent read-only audits completed during this work: `WeakPoynting/Lipschitz.lean` has correct reflected derivative sign, actual Lipschitz integration by parts, mollifier support control, a.e. derivative convergence, dominated convergence, and real/Hermitian Maxwell applications. `StaticCoefficient.lean` correctly constructs the actual square-root coefficient multiplier and weighted static block; its dynamic perturbation remains explicitly abstract and norm-small. Both authors and the parent were notified; their sources were not edited.
