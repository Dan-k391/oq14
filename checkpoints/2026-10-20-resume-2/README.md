# Paused OQ14 resume checkpoint (second October20 checkpoint)

Read `work/RESUME.md` for the immutable resume instructions and `manifest.json`
for exact hashes/status. `work/` preserves new proof drafts and reviews without
registering unfinished sources. `evidence/` preserves targeted logs and the
clean2234 PDF/diagnostics. The2234 aggregate was stopped and is not certified.
The last coherent release is1660; the last completed clean proof build is2033.

Original working files remain in place. `restore-work.ps1 -RelativePaths
lean/SomeMissingFile.lean` restores explicitly named missing files only and
refuses overwrites/path escapes. Tool binaries and dependency caches are not
included. Resume only when the user asks.
