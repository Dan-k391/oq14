# Lean formalization audit

The compiled project is `lean/`. It covers ten stable operator and integral
theorems, with exact names and mathematical coverage in `lean/README.md`.
It does not formalize the full Maxwell channel target or the hotspot PDE.

## Toolchain and evidence

- Lean 4.19.0, Windows x86_64 GNU release, compiler commit 6caaee842e94.
- Lake 5.0.0-6caaee8.
- mathlib v4.19.0, commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- All package revisions are pinned in `lean/lake-manifest.json`.
- Successful compiler output and axiom reports: `lean/logs/clean-build.txt`.
- Source and manifest SHA256 plus exact build provenance:
  `lean/logs/provenance.json` (produced by `lean/build.py`).

The source was actually compiled, not merely drafted. Initial elaboration
identified a notation error in the complex inner-product expressions; it
was corrected before the successful clean build. All ten final declarations
report exactly `[propext, Classical.choice, Quot.sound]`. The build script
rejects unproved declarations and any additional reported axioms.

## Scope checks

- Finite-dimensionality is proved explicitly before interpreting finrank;
  the infinite-dimensional convention `finrank = 0` is not used as a shortcut.
- The approximation threshold is strict and applies to the completed map.
- The lower bound and bypass estimates quantify every coherent vector.
- The compression map is explicitly contractive.
- The bypass theorem includes actual measure-theoretic integration, with
  integrability assumptions visible in its statement.
- No unknown Maxwell realization, approximation bound or PDE theorem is
  introduced as a formal axiom or disguised as a completed theorem.

## Dependency and cleanup policy

Only proof source, package files, small logs, and reproduction scripts belong
in the release. `.tools/lean` and `lean/.lake` contain approximately 2.27 GB
and 1.83 GB respectively in this run and are excluded. The former contains
downloaded compiler archives, the portable compiler and download cache; the
latter contains dependency repositories and compiled library artifacts.
Empty provisional `lean/toolchain` and `lean/vendor` directories were removed.

The clean build deletes only the current project's `.lake/build`, after
checking the resolved path stays within the Lean project. It retains the
pinned dependency cache. A clean repository checkout can reuse these
dependencies or fetch them again from the locked upstream revisions.
The portable script also verifies each installed dependency HEAD and the
absence of tracked dependency modifications using read-only Git commands.
Its `--log-dir` option directs a new build's evidence outside the tracked
source tree; provenance includes the source commit and dirty flag.

## Independent finite-three-dimensional hotspot review

After completing the Lean source, independently reviewed
`manuscript/sections/hotspot_closure_audit.tex`. No substantive gap found in
the stated driven theorem with 3D balls projected into a planar patch.
Checked the angular Rayleigh test, forced radial coefficient signs,
small-frequency local correction, distributional dyadic volume operator,
uniform small-contrast inverse, finite-power Herglotz normalization,
Maxwell total-field Runge duality and fixed-interface rounding estimates.
Verified that Corollary 3.4 in the author-hosted Costabel–McIntosh paper
provides the H1-to-H2 regularized lifting used on a ball:
https://costabel.perso.math.cnrs.fr/publis/PoiBogdeRhv2.pdf

Suggested stating explicitly that the approximation balls lie inside the
comparison ball, as in the actual construction. The modal problem remains
unproved. This was an independent analytic review only; none of that new
PDE argument is included in the compiled Lean coverage.
