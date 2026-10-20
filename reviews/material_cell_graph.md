# MaterialCellGraph — geometric bridges, reachability and actual AE covers

Source: `lean/MaterialCellGraph.lean`

SHA256: `7E188A55B8F88825BEEF42A27F4AFB2E06F5A4C1CBBFB11D4090A87C045EA79E`

Evidence: `lean/logs/material-cell-graph-check.log`. Final compile exited
zero without warnings, created an importable object (129032 bytes), and
emitted seven selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

A Bridge U V is an actual connected open spatial set B, covered almost
everywhere by U union V, with nonempty B-intersection with each set. It
does not assert a differential equation, material coefficient, or field
continuation statement. The openness and connectedness of the material
cells themselves remain separate hypotheses for the actual PDE theorem.
Bridge symmetry is proved by interchanging the two overlaps and the union.

An ordinary Relation.ReflTransGen induction propagates any explicit
property along a bridge path. A second theorem proves path reversal from
actual bridge symmetry. These are generic graph facts; their property
step must be independently supplied and is not a final Maxwell premise.

The AE-cover results prove global zero from actual restricted-measure AE
zero on every cell and an actual AE cover of space. A countable-index
version combines countably many exceptional null sets. The general
open-cell version allows an arbitrary index type: a genuine countable
open subcover has exactly the same union, so only countably many cellwise
AE statements are combined. No uncountable union of null sets is used.

The final abstract wrapper composes the explicit property step with graph
reachability, then applies the proved actual AE-cover result. It does not
claim an actual material family has bridges, that all its cells are
reachable, or that its Maxwell fields satisfy the property step. Those
are separate concrete geometry and PDE obligations.

Self-review checked bridge symmetry, path endpoint orientation, countable
AE quantification, measurability of the open cells and their union, exact
countable-subcover equality, and the actual AE-cover hypothesis. No
continuation conclusion is introduced as an unstated assumption.

Root independently read the complete final source at the recorded hash
and passed all seven exports. Source frozen. Root independent compiler
confirmation was pending when this review was recorded.
