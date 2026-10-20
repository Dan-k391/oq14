# Injective compact-operator alternative

Source: `lean/CompactAlternative.lean`.

SHA256: `4ABC82B7FD4FF2F0FDF40DE02B783924F0E344D13BFD5140A26A61348FDDBEA5`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). All seven theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full-source audit passed. The source is frozen at the hash above.

For an injective identity-minus-compact map on a complex Hilbert space, the genuine compact-subsequence norm gap makes every power bounded below, hence its range closed. Failure of surjectivity forces strictly descending power ranges. Orthogonal projection selects a unit vector in each range perpendicular to the next. The compact operator preserves these ranges, and its images of the selected vectors have pairwise distance at least one. Compactness supplies a convergent subsequence, contradicting that separation.

The final theorem proves injectivity implies surjectivity. It assumes genuine operator compactness and Hilbert completeness, with no alternative, closed-range, or surjectivity premise. The inherited kernel/range file is unchanged.
