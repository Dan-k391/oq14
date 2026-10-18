# Div–curl identity: frozen direct-build checkpoint

`lean/WeakPoynting/DivCurl.lean` is frozen at SHA-256 `20c03d9adf1778f494abd6222d0c8eebdab03100bfe7d0fa7c69301c7a24c3cb`. Its direct Lean 4.19.0 compilation exited zero, with six selected exports depending only on `propext`, `Classical.choice`, and `Quot.sound`. Complete output and source hashes are in `lean/WeakPoynting/divcurl-verification.txt` and `divcurl-provenance.json`. Parent integration and independent review remain separate from this direct-build evidence.

The principal result, `OQ14.DivCurl.schwartz_divcurl_energy`, proves the exact identity for actual complex Schwartz vector fields on Euclidean three-space: the sum of squared L2 norms of all nine coordinate derivatives equals the sum of squared L2 norms of the three curl components plus the squared L2 norm of the divergence. It uses actual Fourier derivative identities and the previously proved scalar Plancherel theorem, followed by a checked pointwise complex algebra identity. Curl, divergence, derivatives, and integrals are the actual analytic operations.

The other selected exports are `scalar_norm_squared`, `schwartz_normSq_integrable`, `schwartz_family_fourier_energy`, `fourier_curl`, and `frequency_energy`, all in namespace `OQ14.DivCurl`.

This module alone does not prove H1 regularity of nonsmooth weak fields. That passage is the unfinished draft described in `reviews/divcurl_resume_checkpoint.md`.
