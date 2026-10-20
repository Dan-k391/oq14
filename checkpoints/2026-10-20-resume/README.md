# Paused OQ14 resume checkpoint

Read `../../RESUME.md` first. This is a recovery checkpoint, not a completed
Maxwell formalization or a new coherent PDF release.

`work/` preserves the exact bytes of every new proof/review and the edited
resume/layout files. `manifest.json` records hashes and verification status.
`evidence/` preserves the successful 2033 clean build and diagnostics and the
failed PDF check. The portable archive additionally contains the committed
project sources. Tool binaries, dependency caches and generated objects are
not included; their pinned identities and existing workspace paths are in
RESUME.md.

The working files remain in place. Do not restore over later work.
`restore-work.ps1 -RelativePaths lean/SomeMissingFile.lean` restores only
explicitly named missing files and refuses overwrites or path escapes.
