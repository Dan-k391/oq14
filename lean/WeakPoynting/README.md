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

There are 39 selected axiom reports across these five new modules. All use only the three standard foundational axioms named above. Companion `*-verification.txt` and `*-provenance.json` files record the dependent-module checks and exact source hashes.

After all roots are registered by the coordinator, the repository's `python build.py --log-dir ../output/lean` performs a clean package build and qualified axiom audit. The additional pinned mathlib import for localization is `Mathlib.Geometry.Manifold.PartitionOfUnity`; it can be prepared with `lake exe cache get Mathlib.Geometry.Manifold.PartitionOfUnity` without changing the lockfile.

These results do not establish boundary traces, a W1,1 plane-slice representative, pointwise flux evaluation on an interface, density on arbitrary domains, Maxwell scattering solvability, radiation conditions, Runge approximation, resonance continuation, or the final OQ14 assertions. The localized proof uses whole-space density after an interior cutoff; it does not assume or prove global smooth density for a general domain. No global L2 or boundary condition is required by the local Poynting and real conservation theorems.
