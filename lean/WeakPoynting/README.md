# Actual smooth approximation in H(curl)

`../WeakPoynting.lean` proves that every whole-space distributional L2 curl graph has smooth representatives converging together with their curls in L2. The approximation is the actual convolution with explicit shrinking normalized smooth bumps. No density theorem or convolution/L2 identification is assumed.

The proof first establishes differentiation and weak-curl commutation for convolution, continuity of the L2 translation orbit, and convergence of its Bochner averages. An absolutely integrable product-space estimate justifies Fubini and identifies these averages with the pointwise smooth convolution. This yields `OQ14.WeakPoynting.smooth_graph_approximation`.

Use the repository's pinned Lean 4.19.0 and locked mathlib dependencies. From `lean/`, run:

```text
lake env lean WeakPoynting.lean
```

`verification.txt` and `provenance.json` record the clean direct compilation of the frozen root source and all 16 selected axiom reports. Each report contains only `propext`, `Classical.choice`, and `Quot.sound`. The source contains no admissions or custom axioms.

The following dependent modules are also frozen and have clean direct compiler/axiom audits:

| Module | Audited exports | Main proved result |
|---|---:|---|
| `WeakPoynting.Green` | 6 | Local bilinear Green identity for arbitrary whole-space H(curl) fields. |
| `WeakPoynting.Poynting` | 5 | Conjugation preserves weak curl; genuine integrable complex Poynting density has integral zero. |
| `WeakPoynting.Local` | 6 | The complex identity holds on any open region, requiring only regional L2 field/curl classes and compact C1 tests supported inside that region. A suitable smooth interior cutoff is constructed and its extension is proved to preserve the tested identity. |
| `WeakPoynting.Conservation` | 6 | For actual almost-everywhere Maxwell curl equations with variable real coefficients, the real time-averaged Poynting vector has zero distributional divergence. The compact-test flux is also proved integrable. |
| `WeakPoynting.Slices` | 16 | Measure-preserving Euclidean plane coordinates and actual Fubini turn regional Maxwell conservation into genuine L1 plane-flux slices and their one-dimensional weak derivative, including transverse flux. |
| `WeakPoynting.Representative` | 13 | Zero distributional derivative implies a.e. constancy by real convolution. Actual L1 primitives, smooth localization, and uniqueness yield continuous flux representatives with exact integral increments and canonical endpoint values. |
| `WeakPoynting.Weighted` | 8 | The actual weak product rule and representative uniqueness give the weighted endpoint law; finite-slab Fubini yields the full gradient-dot-flux volume formula directly for regional Maxwell fields. |

There are 76 selected axiom reports across these eight new modules. All use only the three standard foundational axioms named above. Companion `*-verification.txt` and `*-provenance.json` files record the dependent-module checks and exact source hashes. The coordinator independently reviews and registers frozen modules for the combined build.

After all roots are registered by the coordinator, the repository's `python build.py --log-dir ../output/lean` performs a clean package build and qualified axiom audit. The additional pinned mathlib import for localization is `Mathlib.Geometry.Manifold.PartitionOfUnity`; it can be prepared with `lake exe cache get Mathlib.Geometry.Manifold.PartitionOfUnity` without changing the lockfile.

The slicing and endpoint results cover **real diagonal flux with compact C1 transverse apertures and compact C1 axial cutoffs**, on every closed axial interval inside an open collar. They prove the substantive one-dimensional W1,1 content as actual L1 functions, their distributional derivative, and the continuous representative's exact increment law. They do not depend on an assumed Sobolev representative or classical derivative of the flux. The continuous trace value agrees with the plane integral almost everywhere; no field trace or original plane-integral equality at every plane is asserted.

The written `ch:fluxlemma` additionally uses Hermitian off-diagonal flux and arbitrary W1-infinity cutoffs. Those extensions remain unformalized. General boundary traces, density on arbitrary domains, Maxwell scattering solvability, radiation conditions, Runge approximation, resonance continuation, and the final OQ14 assertions are also not established here. The localized proof uses whole-space density after an interior cutoff; it does not assume global smooth density for a general domain. No global L2 or boundary condition is required by the local Maxwell theorems.
