# Clean release verification: 3917

October 22, 2026. Source and local tag `oq14-maxwell-foundations-3917` identify
`e7d42ab2f86e8c23a992558bf5d89a42538c4347`.

The separate clean checkout rebuilt all 393 project modules from an empty
project build directory. All 3917 selected reports passed the foundation
audit; nine installed dependencies match their pinned revisions. No project
proof placeholders or added axioms occur. The clean source provenance was
captured before compilation. The invocation wrote its logs to the default
legacy directory; those outputs were copied to `output/lean/` and verified
before restoring only the two generated legacy log paths to the tagged
source. The checkout was clean for packaging.

All 15 diagnostic groups passed. The matching 112-page PDF passed TeX
reference, citation and overfull-box checks. Pages 106, 107, 108, 109 and 112
were rendered and inspected. The final bibliography item occupies page 112;
this is readable but should be improved in the next typeset revision.
PDF SHA256:
`3ad0eff586c16beaa9a80a7e4f00c5d42ec0d8416d10845baf200218902d3338`.

The matching delivery archive is 8885736 bytes, SHA256
`1f29974477832b9c2b158dd2823ec02990821c5d5f54c284a7845a815be19747`.
Fourteen matching artifacts are preserved under
`output/checkpoints/oq14-maxwell-foundations-3917/`; matching copies are at
top-level `output/`. Archive CRCs and copied hashes passed. Prior releases
remain preserved, and no external publication occurred.

This is an audited intermediate formalization, not complete OQ14 Lean
closure. The declaration scope is recorded in
`reviews/actual_constructions_3917.md`. Subsequent unregistered proofs are
being independently audited separately; none is credited to this release.
