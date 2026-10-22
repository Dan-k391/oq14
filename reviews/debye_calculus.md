# Independent audit of actual local Debye differential calculus

Source: `lean/DebyeCalculus.lean`.
SHA256: `3F5FA7D236832BD4A1F1F4256FD8B6411B386BD380D0DD1D1C436FF9B78FE5A9`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Exit 0, no warnings, and all fifteen reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/DebyeCalculus-independent-continuation.log`.

The partial derivatives are actual real Frechet directional derivatives.
Their second/third commutations follow from actual smoothness and local
eventual equality. The actual Laplacian commutes with actual curl; actual
divergence of curl vanishes. The product formula Delta(x_j f) = x_j Delta f +
2 partial_j f is derived with the actual coordinate derivatives.

On an actual open domain, these identities imply that toroidal(f)=curl(x f)
is smooth and inherits the scalar Helmholtz equation. Its actual double curl
equals q^2 toroidal(f). The proof uses open-domain neighborhoods when
differentiating local equations, rather than a pointwise equation alone.

The scalar smoothness and scalar Helmholtz equation are explicit hypotheses
here. They still need to be discharged for actual regular/outgoing scalar
waves. No spatial Maxwell reconstruction, normalization, interface matching,
or completeness conclusion is claimed by this calculus module.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 15 reports using only standard foundations. Final source SHA256 `3f5fa7d236832bd4a1f1f4256fd8b6411b386bd380d0dd1d1c436ff9b78fe5a9`. Independent log: `lean/logs/DebyeCalculus-independent-continuation.log`; log SHA256 `ee1b44bcea90fb077eb3f39bce825032a78f8d9cfa2762f37b1a096a54f6ad54`. This certifies the stated scope, not either complete OQ14 construction.
