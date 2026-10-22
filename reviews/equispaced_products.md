# Genuine factorial products for literal interpolation nodes

Source: `lean/EquispacedProducts.lean`.
SHA256: `3CC95A69B7EAF401FC9A3AD25E0A850015DB3FF1D3638F52F6D4DBB934113519`.

Author final target plus object compiler exit 0, no warnings. Object 293016 bytes. Seven selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/EquispacedProducts-final.log`. Forbidden-token scan passed.

The literal nodes are node_l(i)=i/(l+1), i in Fin(l+1); injectivity, nonnegativity and node<1 are proved, including l=0. The actual full integer distance product with its self factor replaced by one is proved equal to i! (l-i)! by induction on l and a genuine finite-last-coordinate split. The descending endpoint product is the actual descending factorial product. Removing the self index and dividing each actual distance by l+1 gives the exact literal interpolation denominator

    product_{j!=i} abs(node_l(i)-node_l(j)) = i!(l-i)!/(l+1)^l.

No separation or denominator conclusion is assumed. This supplies the factorial cancellation needed to prevent superexponential interpolation estimates; coefficient norms and tensor interpolation are successors.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `3cc95a69b7eaf401fc9a3ad25e0a850015db3ff1d3638f52f6d4dbb934113519`. Independent log `lean/logs/EquispacedProducts-root-audit.log`, SHA256 `bf36b730730d34c5664635e08d15de0faa01ced1c785bef1f16c0a2fb3adec36`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
