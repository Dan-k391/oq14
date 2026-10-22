# Independent audit: DebyeMaxwell

Frozen source: lean/DebyeMaxwell.lean.
SHA256: 5BF62031A047FB57AD9696D9DDA79E975AA0F2ABB8BDF43BE2E826344E0C4486.

Independent complete-source mathematical review and pinned Lean compiler PASS.
The compiler exits 0 without warnings; all four exported reports use only
propext, Classical.choice, and Quot.sound. Log:
lean/logs/DebyeMaxwell-independent-continuation.log.

The actual TE electric field is curl(x f), and its magnetic companion is
-I/k times its curl. The TM fields are curl(curl(x f)) and -I k epsilon
curl(x f). The actual Euclidean Frechet curls satisfy both complex Maxwell
curl equations on the open region. Real-parameter versions are derived by
coercion. Signs agree with curl E = I k H and curl H = -I k epsilon E.

Smoothness, the literal scalar Helmholtz equation, and q squared = k squared
epsilon are explicit hypotheses. TE additionally requires nonzero k. There
is no supplied Maxwell conclusion. The file does not yet instantiate actual
regular/outgoing scalar waves, radial interface matching, or reconstruction.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 4 reports using only standard foundations. Final source SHA256 `5bf62031a047fb57ad9696d9dda79e975aa0f2abb8bdf43be2e826344e0c4486`. Independent log: `lean/logs/DebyeMaxwell-independent-continuation.log`; log SHA256 `2d01ab5d059ac6ad4d3deac01c1796156b1b0585ad954fed0f4adda23e5c94c4`. This certifies the stated scope, not either complete OQ14 construction.
