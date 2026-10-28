# Modal item 2 without transcendence: a degeneration sketch (DRAFT, unverified)

Author: root (Astra), 2026-10-25. Status: mathematical sketch only. Nothing here is formalized, audited or claimed; it records a candidate route so that the closure assessment states the modal block precisely. It does not change the verdict: full OQ14 closure is not claimed.

October 27 review: the bounded-branch argument below is invalid near z = 0.
For fixed n > 1 the degree-one rational pole function tends to 1 as z tends
to zero; the displayed lower bound proportional to 1/(n−1) is not uniform on
compact sets containing zero. A replacement must use the regularized actual
determinant to exclude zeros uniformly near (n,z)=(1,0), and then compactness
away from zero. Stage 57 now independently verifies this replacement in
`ModalDipoleOrigin`, including compact zero exclusion. `ModalDipoleInfinity`
also verifies the exact scaled quotient limit, modulus bounds and unit-phase
limit at inverse frequency zero. This draft itself remains unverified: the
algebraic-branch continuation and nonidentity arguments are still missing.
The spherical volume operator must be restricted to
the selected axisymmetric electric sector before claiming rank-one simplicity.

## The obstacle

`reviews/modal_closure_scope_2026_10_24.md`, item 2: for the modal device one needs a simple high-Q zero `z` of `tmDet 1 n` that is not a zero of `tmDet j n` for any degree `j ≠ 1`. Per pair of degrees the coincidences are finite (`ModalRational.finite_common_zeros`), and for algebraic `n` a coincidence forces a nonzero algebraic `a = 2 i n z` with `exp a` algebraic (`ModalAlgebraicity.common_zero_exponential_obstruction`), which contradicts Hermite–Lindemann; the pinned Mathlib has only the analytic half of that theorem, and the project's no-axiom rule forbids assuming it. The notes also record that a genericity argument in `n` fails at the countability step: a countable union of finite coincidence sets cannot be excluded from the countable set of candidate zeros by counting.

## Structure used

The exact factorization in `ModalAlgebra.tmDet_exp_factorization` is
`tmDet l n z = ((-i)^(l+1)/2) exp(i(1-n)z) (cPlus l n z exp(2 i n z) + cMinus l n z)`.
The prefactor is nonzero, so zeros are equivalent to the vanishing of the
parenthesized expression. The coefficients are finite Laurent expressions in
n and z, not the determinant itself. Clearing denominators gives the polynomial
elimination equation. At n = 1 and z nonzero the degree-one determinant is the
Wronskian constant. The earlier claim of uniform ratio blow-up on arbitrary
bounded z sets is withdrawn; in particular it cannot be used when z tends to
zero. Large-z bounds uniform in n near 1 and their phase behavior still need
proof, rather than only fixed-n asymptotics.

A coincidence of degrees `1` and `j` at `(n, z)` eliminates the exponential: `P_{1j}(n, z) := B_1 A_j − B_j A_1 = 0`, a polynomial in `(n, z)` after clearing `1/z` (nonzero because the leading asymptotics distinguish the degrees: `reviews/channel_next.md`, "rational asymptotic distinguishes every angular order").

## The sketch

Fix a degree `j ≠ 1`. The roots of `P_{1j}(n, ·)` are finitely many algebraic branches `z_i(n)`. The bad set `N_j = {n : some branch z_i(n) is a zero of tmDet 1 n}` is the zero set of `h_i(n) = exp(2 i n z_i(n)) − R_1(n, z_i(n))` along each branch, which is analytic off the finitely many branch points; so `N_j` is countable unless `h_i ≡ 0` on an interval of some branch. Claim: `h_i ≡ 0` on an interval adjacent to `n = 1` is impossible, so by analytic continuation along the branch it is impossible on any interval, and the union of the countable sets `N_j` over `j` is countable; any `n` in `(1, n_1]` outside it (an uncountable set minus a countable one) gives all-degree isolation for every zero of degree 1 at that index. (Simplicity of the chosen zero is already available per degree: `ModalExistence`, `ModalAsymptotics`.)

Proof of the claim by degeneration `n → 1⁺`, with `w(n) = z_i(n)` an algebraic branch satisfying `exp(2 i n w) = R_1(n, w)` identically:

- Case `w(n)` bounded as `n → 1`: the former ratio-blow-up argument is invalid.
  The needed replacement is uniform zero exclusion for the actual determinant
  on each bounded z set, including its removable value at z = 0. This draft
  does not prove that statement.
- Case `|w(n)| → ∞`: an algebraic branch tending to infinity does so at least at a polynomial rate: writing `v = 1/w` and dividing the defining polynomial by the maximal power of `v`, `Q̂(n, v(n)) = 0` with `Q̂(1, 0) = 0`, `Q̂(1, v) = v^μ u(v)`, `u(0) ≠ 0`, gives `|v(n)|^μ |u(v)| = (n − 1) |S(n, v)|`, hence `|w(n)| ≥ c (n − 1)^{−1/μ}`. (This replaces Puiseux expansions by one elementary estimate.)
  - If `Re w(n)` is unbounded near `n = 1`: by continuity and the intermediate value theorem the phase `exp(2 i n Re w(n))` takes every unit value in every neighborhood of `n = 1`, while by fact (ii) the phase of `R_1(n, w(n))` converges (since `|w| → ∞` along the whole approach); the modulus identity `exp(−2 n Im w) = |R_1|` makes the phases equal. Contradiction.
  - If `Re w(n)` is bounded: then `|Im w(n)| ≥ c (n − 1)^{−1/μ} − C`. If `Im w → −∞` then `exp(−2 n Im w) ≥ exp(2c (n − 1)^{−1/μ} − C') ≫ C/(n − 1) ≥ |R_1|` (fact (i), large `|z|`). If `Im w → +∞` then the left modulus tends to `0` while `|R_1| ≥ c'/(n − 1) → ∞`. Either way a contradiction.
- The case split "`Re w` bounded or unbounded near `1`" is exhaustive, and the remaining mixed behaviours are covered by the two sub-cases because they only use unboundedness of `Re w` or of `|Im w|`.

## What a formalization would need (not attempted)

Explicit forms of `A_1, B_1` with fact (i) checked by computation; the polynomial `P_{1j}` nonzero for every `j` (the asymptotic-distinction lemma, degree by degree, uniformly in `j`); continuity and analyticity of root branches of a two-variable polynomial off its discriminant (Mathlib has the implicit function theorem and `Polynomial` root bounds; continuity of roots as a multiset in the Riemann sphere would have to be built); the elementary polynomial-rate lemma; the intermediate-value phase argument; and the final countability selection (`Set.Countable` union, an uncountable interval minus a countable set is nonempty). This is a self-contained analysis project of several modules, independent of number theory. It would settle item 2 only; items 1 (transfer of the sphere mode to the volume operator, needing the complex-frequency outgoing representation formula) and 3 (coefficient continuation, rounding convergence, finite assembly) remain large.
