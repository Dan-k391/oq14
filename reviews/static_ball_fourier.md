# Genuine Fourier identification of weak L2 derivatives

Source: `lean/StaticBallFourier.lean`.
SHA256: `54B4E0EFB67BA888E5204C81A4DD6FCDA6B3AF471EA9E63C6DDD7F442301D620`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all three reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticBallFourier-final.log`. Root independent full-source
mathematical and pinned compiler review PASS at the same hash, no warnings
and all three standard-only reports (session 50993).

The generic theorem assumes actual Schwartz weak derivative pairings between
two genuine L2 elements. It proves, rather than assumes, the Fourier relation
Hhat(xi) = (2 pi i) xi_i Ghat(xi). The proof uses actual bilinear Plancherel
pairings, the already proved inverse Fourier derivative of Schwartz tests,
and the compact smooth annihilator theorem. The unbounded coordinate times
Ghat is only placed in locally integrable functions; L2 membership of that
product is not assumed. Local integrability follows by multiplying the
actual L2 representative by an actual continuous coordinate function.

Applying the generic theorem to the proved ball-gradient weak derivatives
gives the actual Fourier Hessian-gradient relation. Identification of this
Hessian with the Newton symbol still needs the symmetry and trace identities.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 3 reports using only standard foundations. Final source SHA256 `54b4e0efb67ba888e5204c81a4dd6fcda6b3af471ea9e63c6ddd7f442301d620`. Independent log: `lean/logs/StaticBallFourier-root-audit.log`; log SHA256 `57fe52226aab367c3645afe6e4f0d29c671cf4fd8c8a819cc686b76ed489f476`. This certifies the stated scope, not either complete OQ14 construction.
