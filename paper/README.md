# Saved manuscript

[Read the current manuscript](oq14-manuscript.pdf) (111 pages).

This PDF includes the revised exposition and both explanatory figures saved at
source commit `f520a315e5bf177dd865e248068a10bb248eb880`. It was built with
Tectonic 0.17.0 on November 13, 2026. The final TeX pass reported no unresolved
references or overfull boxes. The opening, figures, and nearby section
transitions were visually inspected.

SHA-256:

```text
c0cdcf52c10c395de49d7cc9a1a471a5437f9bddc3cea477403a972fdc5b6b98
```

The [build manifest](build-manifest.json) preserves the source hashes and the
working-tree status exactly as recorded. Its `dirty_worktree: true` flag reflects
local untracked research files; all manuscript sources used for this build are
committed at the source revision above. Compilation and layout checks do not
constitute a new mathematical review.

The [older frozen release PDF](../checkpoints/2026-11-13-closure-release/artifacts/oq14-manuscript.pdf)
has 104 pages and its own clean-checkout provenance. It remains unchanged.
The final formal proof audit is linked from the [main README](../README.md).

**Full closure of original OQ14 is not claimed.** Read the README's scope
qualifications together with the theorem statements before citing the results.

To rebuild, run `python scripts/build.py` from the repository root. That command
writes to ignored `output/pdf/`; it does not replace this saved snapshot.
