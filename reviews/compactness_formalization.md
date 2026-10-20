# Concrete weak H1 compactness

`lean/WeakPoynting/Compactness.lean` is frozen at SHA-256
`28278a61f0a3489ceea09e2ec78f7443d6bd12831f53ad9164610ec4eda054d7`.
All ten selected exports directly compile without warnings and use only
`propext`, `Classical.choice`, and `Quot.sound`. Full output and source-scoped
provenance are recorded in `compactness-verification.txt` and
`compactness-provenance.json`. The pinned official Arzelà–Ascoli dependency
required one missing cache archive; compiler and dependency pins are unchanged.

The final theorem `weakH1Ball_compactClosure` proves compact closure in the
actual whole-space L2 space for classes with:

- a common bound on their L2 norms;
- essential support in a fixed closed Euclidean ball;
- three genuine distributional weak partials in L2, with a common bound on
  the sum of their L2 norms.

The proof constructs the same actual normalized smooth convolutions used
in the weak graph approximation. For a fixed kernel, Cauchy–Schwarz bounds
its values and all first derivatives uniformly in the input family.
The support bound follows directly from the convolution integral and the
triangle inequality. The pinned Arzelà–Ascoli theorem supplies compact
closure of restrictions to the common closed ball.

An actual L2 indicator of that ball bounds the whole-space L2 distance by
the restricted uniform distance. Finite covers transfer precompactness to
the fixed convolution image. The independently proved quantitative
mollification error is uniform on the weak derivative ball, and a second
finite-cover argument proves total boundedness of the original family.
Completeness of L2 supplies compact closure.

No compact embedding, H1 translation bound, smooth density, or convergence
of derivatives is assumed. This is a compact-support whole-space theorem.
Its application to regional Maxwell fields needs the separately proved
interior cutoff and local derivative estimates; boundary compactness and
scattering existence are not claimed here.

Independent full source reviews by the coordinator and hotspot agent passed.
Both checked the actual support, norm domination, finite-cover transfer, and
uniform approximation steps; no substantive defect was reported.
