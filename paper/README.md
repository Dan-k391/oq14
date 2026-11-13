# Saved manuscript

[Read the current manuscript](oq14-manuscript.pdf) (113 pages).

This snapshot was built on 13 November 2026 with Tectonic 0.17.0 and Python
3.14.2 using `python scripts/build.py --cached`. The final TeX pass reported
no unresolved references or citations and no overfull boxes. The abstract,
introduction, both figures, verification appendix, and bibliography were
rendered and visually inspected. Compilation and layout checks are not a
mathematical proof review.

SHA-256:

```text
4404858348ef1822812c899a07241adb53a8f52799f465232701850bad2816d8
```

The [build manifest](build-manifest.json) records the exact SHA-256 hash of
each manuscript source and of the PDF. At build time the working tree
contained the article edits on top of checkpoint
`ba7691ed84b320341103e58be5842638170418a3`, so the manifest correctly says
`dirty_worktree: true`: that checkpoint alone is not the source of this
PDF. The per-file hashes identify the actual built sources, which are saved
with this snapshot in the subsequent article revision commit.

The [older frozen release PDF](../checkpoints/2026-11-13-closure-release/artifacts/oq14-manuscript.pdf)
has 104 pages and its own clean-checkout provenance. It remains unchanged.
The final formal proof audit is linked from the [main README](../README.md).
This editorial revision did not rerun that audit.

**Full closure of original OQ14 is not claimed.** See the
[editorial and mathematical review notes](EDITORIAL-NOTES.md) for outstanding
author, reference, and proof-review issues.

To rebuild, run `python scripts/build.py` from the repository root. That command
writes to ignored `output/pdf/`; it does not replace this saved snapshot.
