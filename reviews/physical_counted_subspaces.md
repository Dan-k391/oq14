# PhysicalCountedSubspaces — author review, 2026-10-27

Author final PASS: pinned Lean 4.19.0, EXIT0, no warnings, one report using only `propext`, `Classical.choice`, `Quot.sound`. Independent review is pending root verification.

- Source: `lean/PhysicalCountedSubspaces.lean`, 149 lines; SHA256 `3647494252B60A17977D663A73CF56BEE83E1B1A4FB4E548FF8762FBC7C85A11`.
- Final log: `lean/logs/PhysicalCountedSubspaces-final.log`; SHA256 `8C78B5AFECAF01295A1429172D458221998230E0E30F7613E1EBF14DAD2442EE`.
- Exit receipt: `lean/logs/PhysicalCountedSubspaces-final.exit.log`, value 0. Generated object exists.
- Complete source/log/object/receipt evidence: `reviews/physical_counted_normalization_author_2026_10_27.json`.

`counted_subspaces_manuscript_physical` corrects the plane-power normalization at the actual manuscript-volume endpoint. At fixed positive frequency, material upper bound greater than one, square side, `0 < τ < 1`, and `0 < η < δ`, every finite dimension has a single finite device and orthonormal incident family. Passage is the physical half-real Poynting integral through `Dsq (L/2)`; bypass is the integral of the absolute real Poynting flux outside that square. The `IsCounted` inequalities quantify every vector in the chosen span.

The construction invokes `CountedSubspacesVolume.counted_subspaces_at_frequency_volume` at doubled raw thresholds `(2η,2δ)`. Before choosing the final indices, it intersects that theorem's eventual counting clause, actual all-input unit throughput, finite basis physical/volume clauses, material bounds, and the independently derived whole-span integrability event. Thus all conclusions concern the same `q,χ,ρ,h,R,A,n,r`, not separately selected devices. The pointwise bypass comparison is applied only after actual integrability is available.

The endpoint retains the original coefficient bounds and dimension, the vacuum weak Maxwell inputs and physical incoming-power limit, the actual complete scattering map and unit throughput for every finite incident datum, and all original per-basis physical-field, legitimate plane representative, frequency-volume solution, weighted-data, and block-invertibility equivalence clauses. It additionally exports whole-plane integrability of the raw complex normal flux, `Re F/2`, and `|Re F|/2` for every vector of the counted span.

Scope remains the existing finite restricted harmonic TE incident sector and literal finite shell-plus-inclusion device. This module does not assert a named even-m basis equivalence, a full incoming-Hilbert-space extension, rates in the two indices, or a support radius common to all dimensions. The original block-invertibility equivalence clause is retained; it is not relabeled as a new unconditional invertibility theorem. Physical-field and volume-solution clauses remain per basis as in the frozen endpoint, whereas counting and integrability hold on the entire span.

The author correction changes only new modules and these author receipts/reviews. No old audited source, registry, RESUME, manuscript, shared configuration, sites, or Git state was changed. Source scan and single-final-newline checks pass. No compiler sessions remain active after the author final run.
