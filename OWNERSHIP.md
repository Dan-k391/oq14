# Concurrent file ownership

The coordinator alone runs Git and owns main.tex, macros.tex, references.bib, problem.tex, verification.tex, ledgers, build scripts, evidence, and integration.
Hotspot agent: manuscript/sections/hotspots.tex and reviews/hotspots.md.
Channel agent: manuscript/sections/channels.tex and reviews/channels.md.
Counterexample agent: manuscript/sections/counterexamples.tex and reviews/counterexamples.md.
Agents must not switch branches, commit, or edit another owner's files.

After the first reviewed milestone was merged, the coordinator took ownership
of the original sections for integration. The renewed disjoint assignments were:
- Hotspot agent: manuscript/sections/hotspot_closure_audit.tex and reviews/hotspot_closure.md.
- Channel agent: manuscript/sections/channel_closure_audit.tex and reviews/channel_closure.md.
- Counterexample agent: lean/ and reviews/lean.md.
Agents could independently review the other files and send corrections to their owner.

The 18 October continuation used these further disjoint assignments:
- Root: modal_spectral.tex, integration, bibliography, ledgers and build audit.
- Hotspot agent: modal_next.tex and its review; temporary authorized correction
  of the F-versus-L issue in modal_spectral.tex; channel_global_attempt.md.
- Channel agent: channel_next.tex and its review.
- Counterexample agent: lean/Maxwell.lean, lean/Maxwell/ and its review only.
Root alone changes Git state and packages the reviewed milestone.
