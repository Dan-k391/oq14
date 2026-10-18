# Lean verification of the stable operator core

The formal source is `OQ14.lean`. Ten theorems compile with Lean 4.19.0
and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`
(the `v4.19.0` tag). `lake-manifest.json` pins every transitive dependency.

## Reproduce

Install the [official Lean 4.19.0 release](https://github.com/leanprover/lean4/releases/tag/v4.19.0)
or use an existing installation selected by `lean-toolchain`. From this
directory, prepare dependencies using the supplied lockfile (keep
`lake-manifest.json` unchanged):

```text
lake exe cache get Mathlib.Analysis.NormedSpace.OperatorNorm.Basic Mathlib.Analysis.Normed.Operator.LinearIsometry Mathlib.Analysis.InnerProductSpace.Basic Mathlib.LinearAlgebra.FiniteDimensional.Defs Mathlib.LinearAlgebra.Dimension.Finrank Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.Data.Real.Sqrt Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
```

Then run the portable clean source build and axiom audit:

```text
python build.py
```

For a portable compiler outside PATH, use
`python build.py --lake /absolute/path/to/lake` (or `lake.exe` on Windows).
The local Windows compiler, when present, is automatically found under
`../.tools/lean/lean-4.19.0-windows/bin`. No global installation is required.
`build.ps1` is an additional Windows-only build entry point; `build.py`
provides the full source-hash and theorem-by-theorem axiom audit.
Use `--log-dir /absolute/output/directory` to preserve the tracked evidence
files during a new clean-checkout build. Git is used read-only to verify
every installed dependency HEAD against the manifest and reject changed
tracked dependency files; `--git /absolute/path/to/git` selects it explicitly.
The output also records the source repository commit and dirty flag.

The build removes **only this package's** `.lake/build`, verifies the pinned
compiler and mathlib revision, runs `lake build OQ14`, and audits all ten
`#print axioms` reports. It retains compiled dependency artifacts, as a
normal clean project build does. The raw successful compiler output is
`logs/clean-build.txt`; exact source and manifest SHA256 hashes, compiler,
and theorem names are in `logs/provenance.json`. Large downloaded tools,
dependency checkouts and compiled caches are excluded from the deliverable.
Do not run `lake update` for a locked reproduction: it is a dependency-update
operation. Lake fetches missing packages for the cache/build command using
the supplied manifest. A clean source checkout may reuse the existing
`.lake/packages` directory (for example with a local directory junction)
while retaining its own freshly rebuilt `.lake/build`.

If the official ProofWidgets release download encounters a transient
network failure during setup, retry `lake build proofwidgets:release`,
then repeat the cache command. This repair does not change the proof source
or dependency revisions.

## Formal theorem coverage

All names below have namespace prefix `OQ14.`.

| Declaration | Verified statement |
|---|---|
| `approximation_kernel_trivial` | A strict operator error below a uniform amplitude lower bound excludes nonzero kernel vectors. |
| `approximation_injective` | The approximating operator is injective. |
| `finiteDimensional_of_approximation` | Finite-dimensional approximation range forces actual finite dimensionality of the domain. |
| `finite_rank_channel_bound` | The resulting dimension is at most the approximation rank bound. |
| `finite_rank_power_channel_bound` | The power formulation uses exactly the strict error threshold `sqrt(tau)` and returns finite dimensionality and dimension at most M. |
| `isometry_perturbation_lower_bound` | Error at most e from an isometry yields amplitude at least `(1-e)` times input norm for every input. |
| `isometry_perturbation_power_threshold` | The strict margin `e < 1-sqrt(tau)` yields power above tau for every nonzero input. |
| `compression_power_threshold` | A contractive output compression satisfying that certificate yields the same lower bound on full output power. |
| `quadratic_flux_norm_bound` | Absolute real quadratic flux is bounded by operator norm times squared input norm. |
| `absolute_bypass_certificate` | Integrating the operator norm gives the coherent absolute-bypass bound, with integrability explicitly assumed. |

The first group formalizes the elementary dimension reduction in the
channel section. The second group covers the unitary/isometry compression
certificate in `cx:compression`. The final group proves the analytic
integration step underlying `cx:absolute-bypass`, in a complex inner
product space over an arbitrary measure space.

Every theorem's reported axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`, the standard Lean/mathlib foundations. There are no
project-specific axioms, admitted proofs, or assumed Maxwell conclusions.

## Explicitly outside the formalization

This is **not formal verification of OQ14**. The source contains no Maxwell
PDE, trace theorem, scattering realization, corner/Runge/rounding proof,
or uniform rank-M approximation construction. In particular, it does not
prove that the approximation hypothesis holds uniformly over the physical
class. It also does not identify a measurable operator-valued flux form
with physical Maxwell traces; that bridge remains a separate analytic
claim. These limits are substantive, not merely implementation details.
