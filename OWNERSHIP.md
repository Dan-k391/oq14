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

The further continuation uses these disjoint assignments:
- Root: lean/HCurlDomain.lean and its evidence, integration and build audit.
- Counterexample agent: lean/HCurl.lean and its evidence, external PDE library audit.
- Channel agent: channel_global.tex and its review.
- Hotspot agent: channel_nonradial.tex and its review.
Frozen files are changed only after notifying the owner and invalidating old hashes.

The latest disjoint assignments are:
- Root: integration of all frozen sources, clean-checkout audits and packaging.
- Channel agent: channel_control.tex and its review (now frozen);
  unrestricted_passage_audit.md for continuing research.
- Hotspot agent: channel_bandlimited.tex and its independent review (now frozen);
  nearby_transducer_audit.md for continuing research.
- Counterexample agent: HCurlCutoff.lean and its evidence (now frozen);
  WeakPoynting.lean, WeakPoynting/ and its review for continuing research.

Further frozen additions are channel_dual_control.tex (channel agent),
channel_passage.tex (root, transcribed from the channel agent's independently
reviewed derivation), and channel_transducers.tex (hotspot agent). Root has
reviewed all three. WeakPoynting.lean and WeakPoynting/Green.lean are frozen
and independently reviewed by root. The formal agent continues in separate
Poynting.lean and Local.lean files. New common-stack Green convergence and
transducer-limit sections remain with the channel and hotspot agents,
respectively. After independent root and cross-agent review, the common-stack
Green and whole-plane limit and the small-inclusion remainder are integrated
with root's channel_unrestricted.tex. They give the written counterexample
for delta>eta and full-scattering output.

Poynting.lean, Local.lean, and Conservation.lean are frozen and reviewed by
root. The formal agent continues in WeakPoynting/Slices.lean. The hotspot
agent continues in the separate ModalAlgebra.lean. Root owns registration,
counts, the claim ledger, and all Git/build/release integration. Active new
Lean work is excluded from clean snapshot builds until frozen and reviewed.
