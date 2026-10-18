# Actual smooth approximation in H(curl)

`../WeakPoynting.lean` proves that every whole-space distributional L2 curl graph has smooth representatives converging together with their curls in L2. The approximation is the actual convolution with explicit shrinking normalized smooth bumps. No density theorem or convolution/L2 identification is assumed.

The proof first establishes differentiation and weak-curl commutation for convolution, continuity of the L2 translation orbit, and convergence of its Bochner averages. An absolutely integrable product-space estimate justifies Fubini and identifies these averages with the pointwise smooth convolution. This yields `OQ14.WeakPoynting.smooth_graph_approximation`.

Use the repository's pinned Lean 4.19.0 and locked mathlib dependencies. From `lean/`, run:

```text
lake env lean WeakPoynting.lean
```

`verification.txt` and `provenance.json` record the clean direct compilation of the frozen root source and all 16 selected axiom reports. Each report contains only `propext`, `Classical.choice`, and `Quot.sound`. The source contains no admissions or custom axioms.

This root module establishes whole-space graph density. It does not establish boundary traces, density on general domains, Maxwell scattering solvability, radiation conditions, or the final OQ14 assertions. The dependent `Green.lean` develops the local weak integration-by-parts identity separately.
