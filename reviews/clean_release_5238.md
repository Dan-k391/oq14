# Clean release verification: 5238

October 23, 2026. The local tag `oq14-maxwell-foundations-5238` identifies
source commit `8a4a8bf4abb15d7ae6f2fc0fa4d63758c3c04248` in root and the
isolated clean checkout `tmp/clean-5238`.

The independent checkout rebuilt all 627 project modules (599 libraries)
from an empty project build directory. All 5238 selected foundation reports
passed, compiler exit zero. All nine dependency repositories match the
lockfile, every source hash matches the clean snapshot, and every project
object exists. Only propext, Classical.choice and Quot.sound occur in the
selected reports. Fourteen legacy tactic-style warnings are byte-for-byte
the same as release 4391; there are no new warnings or compiler errors.
Root compiler caches were untouched.

All 15 diagnostic groups passed at the same source revision. The matching
113-page PDF passed reference, citation and overfull-box checks. Corrected
verification pages 98 and 106–113 were rendered and inspected; they are
legible without overlap or clipping. PDF SHA256:
`611c64b2041ace2988d2db781246a4a7dfb0a05c867c28ad09948ceb7b3b649d`.

The delivery archive is 14974809 bytes, SHA256
`ba907a88acbb9f69821d96adef7b35f4d0a80e30322454812debee14832db1c7`.
All fourteen artifacts are preserved under
`output/checkpoints/oq14-maxwell-foundations-5238/` and copied to top-level
output. Archive CRCs, Git bundle verification, both local tag targets and
copied hashes passed. The preservation receipt records all fourteen hashes
and the complete validation result. Earlier releases remain preserved.
No external publication occurred.

This is an intermediate formalization, not full OQ14 closure. Newer targeted
proofs in the active October 23 working tree are not included in this release.
Their independent evidence is recorded separately in
`tmp/audited_after_5238.json`. Full physical construction assembly and the
complete modal and channel proofs remain active work.
