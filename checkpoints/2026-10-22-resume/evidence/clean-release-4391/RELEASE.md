# OQ14 reviewed research release

Source branch: 
Source commit: c597c535c9a751fccbf3e9a0d644721326ceda26
Milestone tag: oq14-maxwell-foundations-4391
Tracked and nonignored untracked working-tree changes: none.

The 113-page manuscript, 15 diagnostic groups, and 4391 audited Lean theorem
declarations were rebuilt from this clean source revision. TeX references,
citations and overfull-box checks passed. Rendered layout was inspected.
Lean used 4.19.0 and the locked mathlib revision; all nine dependency
repositories were checked against the lockfile. The proof package was
rebuilt with an empty root build directory and retained pinned dependency
caches. Only propext, Classical.choice and Quot.sound occur in axiom reports.

The finite three-dimensional driven and genuinely normalized modal hotspot
theorems have complete written proofs under their stated conventions. The
modal theorem includes arbitrary high Q, fixed real pole frequency, common
ordinary material bounds and actual maxima in the prescribed plane patch.
The explicitly quantified unrestricted fixed-section channel assertion is
disproved for every fixed delta>eta>0, with the complete scattering map
selected as output. Stronger bypass or receiving-output versions remain
separate questions. The construction is an analytic proof, not a numerical
many-channel simulation. Lean checks the scoped declarations listed in its
README and build provenance, including actual weak local power conservation.
Actual interface continuation, geometric-partition volume uniqueness,
finite radial geometry and constructed physical scattering fields are
formalized. The complete channel and modal constructions remain unfinished;
arbitrary outgoing PDE equivalence and the remaining continuum bridges
are not supplied by these scoped results.

The source/ directory contains all tracked sources, build instructions,
proof reviews and research-stage evidence. Release artifacts and clean
build provenance are under artifacts/. The Git bundle preserves all
branches, tags and commits. Downloaded papers, compilers and dependency
caches are excluded. No repository was published.

Restore Git history with:
    git clone artifacts/oq14-history.bundle oq14
Then follow source/README.md and source/lean/README.md to reproduce builds.

Some source-tree research logs deliberately identify an earlier dirty
research run. The clean release records under artifacts/ are authoritative
for this milestone. Compilation and numerical diagnostics do not certify
the handwritten continuum proofs.
