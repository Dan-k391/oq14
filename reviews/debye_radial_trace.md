# Independent audit: DebyeRadialTrace

Frozen source: lean/DebyeRadialTrace.lean.
SHA256: 1383732788473EE2BC531D2135FADC9231526BDBA9F87F9D419B5C93D457F374.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all eleven reports standard-only.
Log: lean/logs/DebyeRadialTrace-independent-continuation.log.

The genuine Frechet derivatives of eta(norm x)*P give the actual toroidal
field eta*(grad P cross x). Genuine second curls, polynomial harmonicity and
the Euler identity give curl M=(r eta'+(l+1)eta)grad P-l eta'/r*x P.
Actual radial contractions and position cross products are then proved,
including x cross M=eta*(r squared grad P-l P x) and
x cross curl M=-(r eta'+(l+1)eta)*(grad P cross x).
The signs agree with the defined order grad P cross x.

Only actual smooth radial eta on positive radii and literal homogeneous
harmonic polynomial properties are supplied. No radial trace, curl,
Maxwell matching, or interface conclusion is assumed. These are pointwise
identities away from the origin; Sobolev transmission and actual state
coefficient identification across an interface remain separate constructions.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 11 reports use only standard foundations. Final source SHA256 `1383732788473ee2bc531d2135fadc9231526bdba9f87f9d419b5c93d457f374`. Independent log `lean/logs/DebyeRadialTrace-independent-continuation.log`, SHA256 `68b594f18ce31d502313063c0b62d822596bb5723542e091e83e181b849b9e98`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
