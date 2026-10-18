# Resume OQ14 from the 2026-10-18 checkpoint

Read this file first. The user requested a checkpoint for easy later
resumption. All proof work is saved and all compiler sessions have ended.
The task is **not complete**. Do not claim complete Lean verification.

## Durable checkpoints

- Git tag `oq14-resume-2026-10-18`: the current source checkpoint, with
  646 registered declarations in 45 modules and the saved continuation work.
  The 107 additions after the preceding release have passed targeted Lean
  compilation and independent source review. A new aggregate clean rebuild
  and updated manuscript rendering are still due for this source checkpoint.
- Git tag `oq14-maxwell-foundations-539`, commit
  `ebaa4753e914ab766c17731b2d24bb961bea38cd`: latest fully packaged clean
  release. All 539 declarations passed the strict axiom audit; all 15
  diagnostic groups passed; the 105-page PDF was rendered and inspected.
- That complete release is in `output/checkpoints/oq14-maxwell-foundations-539/`
  and also in the top-level `output/` delivery files. Preserve its coherent
  source/PDF/log provenance until a replacement is fully rebuilt.
- A portable source/history checkpoint is saved under
  `output/checkpoints/oq14-resume-2026-10-18/` after the source commit.

Verified release delivery SHA256:
`67a86e8db1bdd33d5bcc5a329ecb6dd25183268488de2a47b289be692c9ea3c4`.
Verified PDF SHA256:
`f8ff329a6fd5bed10b669dacdf9e83dab1cbeae132029ec19e5d1988ce775d16`.

## Scientific status to preserve

The unrestricted fixed-section channel finiteness assertion is disproved
in the written manuscript for every fixed delta>eta>0 when the selected
output is the complete scattering map. The counterexample uses finite,
ordinary positive dielectrics at common frequency and material bounds.
Stricter bypass thresholds, prescribed receiving outputs, and fixed total
support are separate questions. Do not broaden the disproof's scope.

The written modal hotspot theorem constructs one genuinely normalized
high-Q mode with arbitrary finite peak count, fixed real frequency, common
ordinary material bounds, and actual maxima in the prescribed plane patch.
These written conclusions have **not** yet been fully formalized in Lean.
No theorem-shaped assumptions or custom axioms may replace the missing
Maxwell existence, interface, scattering, rounding or resonance arguments.

## Checked additions since the 539 release

The registered source total is 646 = 539+107. The additions are:

| Module | Exports | Actual result |
|---|---:|---|
| HeatFourier | 26 | L1 convolution Fourier identity, Gaussian transform and Newton scale formulas |
| NewtonFourier | 11 | Absolute scale-space Fubini and actual Newton Fourier identity |
| NewtonHessian | 10 | Full distributional Hessian, negative longitudinal symbol, Delta N=-delta |
| DynamicIntegrability | 5 | Actual dynamic remainder entrywise local L1/L2 |
| KernelEstimates | 4 | Exact inverse-radius ball integrals and entrywise quadratic mass bound |
| ModalDipole | 14 | Actual complex-frequency Maxwell dipole curls away from center |
| ModalInterface | 23 | Actual spherical tangential matching equivalence and nonzero high-Q fields |
| WeakPoynting/Energy | 10 | Actual weak reactive identity and Caccioppoli estimate |
| WeakPoynting/EnergyLocalization | 4 | Actual local estimate with coefficient 2+4d²/(omega²m) |

All selected reports use only propext, Classical.choice and Quot.sound.
Detailed reviews are under `reviews/`; `lean/README.md` and the manuscript
verification section record the precise scope. The 646 source count must
not be described as a completed aggregate clean release yet.

## Saved continuation work

To keep the registered Lean tree buildable, unfinished/unintegrated files
were moved without modification to
`checkpoints/2026-10-18-resume/work/`, preserving their original relative
paths. Restore only the files you are actively continuing. The supplied
`restore-work.ps1` refuses to overwrite an existing file. Older agent resume
notes refer to the original paths, which become valid after restoration.

| Track | Saved status | Resume note |
|---|---|---|
| NewtonConvolution | Draft; three local elaboration errors | `reviews/newton_convolution_resume.md` |
| ModalOrigin | Draft; three local algebra/elaboration errors | `reviews/modal_origin_resume.md` |
| WeakPoynting/DivCurl | Six direct-checked exports, not yet root-reviewed or registered | `reviews/divcurl_formalization.md` |
| WeakPoynting/DivCurlCompact | Draft; three errors, actual H1 construction still to finish | `reviews/divcurl_resume_checkpoint.md` |
| PointSingularity | Root draft; one current elaboration error, main IBP proof not written | Below |

PointSingularity should prove integration by parts across a single point
in R3 by coordinate Fubini. For almost every transverse coordinate q!=0,
the entire coordinate line misses the origin, so ordinary one-dimensional
IBP applies. Assume actual off-origin differentiability and genuine
integrability of f'g, fg', fg; do not assume the target weak identity.
The saved draft constructs the volume-preserving split, affine coordinate
line, its actual derivative, and nonzero-line argument. Its last compile
failed at line 28: dependent `Fin.insertNth 0 q j` needs explicit real
family/type arguments. `join_hasDerivAt` uses a single function equality
rewrite to avoid recursive rewriting of the base point. After repairing
this, copy the actual Fubini proof pattern from mathlib's
`Analysis/Calculus/LineDeriv/IntegrationByParts.lean` but exclude the null
transverse singleton. Apply the resulting lemma twice to phi_k-N, deriving
integrability bounds first, to show its weak Hessian has no extra contact
term. This is needed for the actual dynamic volume kernel.

## Resume order

1. Check this Git tag and the archived work manifest. Preserve source pins.
2. Restore the tracks being continued and delegate them in parallel.
3. Finish/audit/register NewtonConvolution, ModalOrigin and the div-curl
   weak-derivative construction; continue PointSingularity separately.
4. Connect actual spatial convolution to the L2 longitudinal projection;
   identify the full outgoing kernel distribution and its bounded volume
   operator. Continue actual weak assembled interfaces and modal isolation.
5. Rebuild registered sources in a clean checkout, run the 15 diagnostic
   groups, rebuild and inspect changed PDF pages, then package a new
   coherent release. Do not overwrite the 539 evidence with mixed versions.
6. Continue all remaining Maxwell/channel/hotspot proof obligations.

## Environment and commands

Workspace: `D:/oq14`; shell PowerShell. Python:
`C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Lean/Lake: `D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe`.
Tectonic: `D:/oq14/.tools/tectonic/tectonic.exe`.
Lean 4.19.0; mathlib v4.19.0 at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependencies are locked.
No dependency upgrade was made. The new removable-singularity dependencies
were fetched from that exact pinned cache.

From the workspace, use the full Python path with:

```text
lean/build.py --lake D:/oq14/.tools/lean/lean-4.19.0-windows/bin/lake.exe --log-dir output/lean
scripts/verify.py
scripts/build.py --cached --tectonic D:/oq14/.tools/tectonic/tectonic.exe
```

Set `TECTONIC_CACHE_DIR=D:/oq14/tmp/tectonic-cache`. Targeted development:
from `lean/`, run `lake env lean Filename.lean`; build registered modules
with `lake build ModuleName` to generate importable oleans. The strict
aggregate audit scans every Lean source under `lean/`, so do not run it
with unverified drafts restored there. Use a clean source checkout instead.
The existing `tmp/clean-checkout` is still at the 539 release; its own build
directory is separate and its dependency directory links to the pinned cache.

The repository was not published. No ongoing jobs or scheduled tasks are
required for this checkpoint. Resume with: "Continue D:/oq14 from RESUME.md."
