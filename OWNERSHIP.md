# Concurrent file ownership

The coordinator alone runs Git and owns main.tex, macros.tex, references.bib, problem.tex, verification.tex, ledgers, build scripts, evidence, and integration.
Hotspot agent: manuscript/sections/hotspots.tex and reviews/hotspots.md.
Channel agent: manuscript/sections/channels.tex and reviews/channels.md.
Counterexample agent: manuscript/sections/counterexamples.tex and reviews/counterexamples.md.
Agents must not switch branches, commit, or edit another owner's files.
