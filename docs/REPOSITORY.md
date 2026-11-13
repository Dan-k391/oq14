# Repository organization

This repository separates current entry points, saved artifacts, and historical
research evidence without relocating frozen checkpoint files. Their recorded
paths and hashes are part of the audit trail.

## Current entry points

Read the root [README](../README.md) first. The canonical mathematics is in
`manuscript/`; Markdown files are indexes and records. The final formal endpoint
is [OQ14Closure.lean](../lean/OQ14Closure.lean). The current saved manuscript is
in [paper/](../paper/README.md).

The [scope index](../PROBLEM.md) and [claim ledger](../CLAIMS.md) distinguish
theorems from their relationship to original OQ14. No claim of full closure of
the original question is made. In particular, the channel output convention,
`delta > eta` restriction, and reciprocal-residue modal normalization must
remain visible when these results are cited.

## Preserved history

`checkpoints/` contains frozen stage records, source inventories, raw evidence
archives, and reviewed releases. `checkpoint/`, `handoffs/`, and `reviews/`
retain earlier continuation and review history. Earlier files may describe
incomplete work, abandoned approaches, or superseded conclusions. Their
presence does not make them current accepted results.

The November 13 release and its original 104-page PDF remain unchanged under
`checkpoints/2026-11-13-closure-release/`. The later manuscript exposition and
two figures were saved separately at commit
`f520a315e5bf177dd865e248068a10bb248eb880`.

## Local working files

The GitHub upload includes the existing tracked history, the revised manuscript,
the two project reading lists, the saved current PDF, and these navigation
updates. It is a curated research repository, not an image of the workstation.

The following remain local:

- Downloaded toolchains and package caches (`.tools/`, `lean/.lake/`).
- Rebuildable products and temporary work (`build/`, `output/`, `tmp/`, compiled
  Lean objects, and untracked diagnostic runs).
- Cached third-party full texts (`sources/cache/`).
- Unaccepted proof probes and unfinished scratch/review files that were already
  untracked before this upload. They have not been deleted or promoted to
  verified results.
- The unrelated `sites/` project.

Existing tracked logs and ZIP files are intentional historical evidence and
remain in Git. Ignore rules apply to new generated files; they do not remove
previously committed evidence.

## Reproducibility

The [paper build manifest](../paper/build-manifest.json) records source hashes,
compiler version, source commit, and PDF hash. Its working-tree flag includes
local untracked files and should be read literally.

The [formal audit](../checkpoints/2026-11-13-closure-release/AUDIT.txt) describes
the final source inventory and logical dependency check. Its replay scripts
retain the original Windows paths and cached dependency assumptions. Preparing
a portable one-command replay of that final aggregate is separate from the
historical foundation build command.

No formal Lean source or frozen proof evidence was changed to prepare this
GitHub upload.
