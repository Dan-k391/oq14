# Independent piecewise Maxwell volume uniqueness audit

Reviewer: continuation_review_sol. Date: 2026-10-20.

Source: `lean/PiecewiseMaxwellUniqueness.lean`.
SHA256: `C500EF26F5B31E5C75479CF3B0E8DCD5610C105C4BB935B97B00D313546184C7`.

Independent pinned Lean 4.19 execution of
`lake env lean PiecewiseMaxwellUniqueness.lean` completed with exit 0.
All five dependency reports list only `propext`, `Classical.choice`, and
`Quot.sound`. The hash remained unchanged after compilation. The complete
source was read, together with the complete MaterialCellGraph,
HomogeneousVolumeUniqueness, MaxwellExteriorRellich and VolumeAlternative
sources and the actual HomogeneousVolumePower field, weak-Maxwell,
local-L2 and exterior-Rellich interfaces. The definition of the bounded
measurable nonnegative susceptibility and actual static preconditioning
factorization were inspected. The regional and scalar continuation proofs
were independently audited in the accompanying continuation reviews.

The geometric Partition structure assumes actual open preconnected cells,
positive constant material values almost everywhere in each cell, an
almost-everywhere cover of space, and finite graph reachability through
actual open connected two-cell bridges. It contains no field-dependent
continuation statement, zero-kernel assertion, or PDE solvability premise.
It does not require the cells to be disjoint, finite, or countable. This
does not cause an exceptional-set problem: the globalization lemma first
extracts an actual countable open subcover before combining AE equalities.

For actual globally locally integrable electric components satisfying the
global weak Maxwell tests, a zero germ at an actual point of one cell gives
AE zero throughout that cell by constant-material weak Helmholtz
continuation. Each Bridge step is then supplied by the actual proved
regional Maxwell interface theorem. Relation.ReflTransGen induction
propagates electric zero to every reachable cell, and the countable-cover
argument gives AE zero globally. The abstract reachable-property lemma is
only topological bookkeeping; its PDE step is fully discharged here.

For a homogeneous actual volume solution, positive real frequency and
compact coefficient support give pointwise electric and magnetic zero
outside the support ball by the actual Maxwell exterior Rellich theorem.
That theorem's zero far-power premise is itself derived from the actual
homogeneous volume equation and weak conservation, rather than assumed
in this new module. The exterior set is open, so the explicitly supplied
point x0 outside the support ball and inside a seed cell supplies a genuine
electric zero germ. Actual local-L2 estimates give local integrability.
The preceding partition theorem therefore forces electric zero globally.

Material self-consistency then makes the actual polarization source zero.
The measure-preserving coordinate equivalence identifies this source with
the actual square-root-weighted L2 unknown. Once that weighted unknown is
zero, the actual static and dynamic volume terms vanish, so the homogeneous
volume equation forces the original unknown to be zero. No division by a
possibly vanishing susceptibility is used.

Finally the proved compactness of the physical dynamic remainder and
invertibility of the positive static block imply the Fredholm alternative.
The newly proved homogeneous uniqueness discharges its former kernel-zero
input. The resulting IsUnit and exists-unique theorems are actual volume
operator conclusions for every L2 datum, with no support-smallness or
contrast-smallness premise.

Precise scope: bounded measurable nonnegative compactly supported scalar
susceptibility, positive real frequency, a supplied Partition of its actual
dielectric, and an actual exterior point in a seed cell. Constructing such
Partition data for an arbitrary claimed piecewise geometry remains a distinct
geometric obligation. This module alone does not prove that all arbitrary
piecewise smooth or rough coefficients admit those bridges, nor does it
complete the final physical channel or modal constructions. Its solvability
conclusion concerns the actual volume equation, rather than every possible
scattering trace/output interpretation.

The new source and its newly inspected graph/adapter sources contain no
standalone axiom/constant declarations or proof-hole tokens. No proof source
was edited. Mathematical audit and independent compiler check: PASS.
