# LocalAEZeroPropagation verification

Source: `lean/LocalAEZeroPropagation.lean`.
SHA256: `CDE28DAFB9EE594655802849CC339C52474996965E4DC7CA49E72D857753B650`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All six selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

A zero germ at x means that the literal function is almost everywhere
zero for actual volume restricted to some positive-radius ball at x.
Restriction to smaller balls proves that every point of such a ball has
a zero germ. Thus the set of zero germs is open.

The local ball propagation premise is explicit: at a point of Omega with
a zero germ, the function is almost everywhere zero on every positive-
radius ball centered there and contained in Omega. With this property,
a sufficiently nearby germ center and its half-radius ball show that
the intersection of the closure of the germ set with Omega consists of
germs. Preconnectedness then gives a zero germ at every domain point from
one initial domain germ.

A genuine countable open subcover of the germ balls is chosen using
second countability of actual Euclidean three-space. Countable union of
the AE equalities and restriction to Omega prove actual almost-everywhere
zero on the entire domain. No measurability or continuity of u is needed
for this measure-theoretic local-to-global step. No PDE-to-local-ball
propagation result is claimed by this topological module; that explicit
premise is discharged separately by actual weak PDE/mollifier arguments.

Independent full-source review requested from root at this hash.
