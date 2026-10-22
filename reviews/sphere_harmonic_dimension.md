# Actual polynomial harmonic dimension bound

Source: `lean/SphereHarmonicDimension.lean`.
SHA256: `964A6697A5C2DDA156C898DC80EBDFEFE7A812A9D430FE3E292F53666E7B3C9B`.

Author final target plus object compiler exit 0, no warnings. Object 100608 bytes; four selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SphereHarmonicDimension-final.log`. Forbidden-token scan passed.

A literal equivalence identifies the bounded exponent vectors d:Fin3->N with d_i<=l with functions Fin3->Fin(l+1). The actual bounded-degree monomial basis therefore gives finrank(restrictDegree l)=(l+1)^3. Actual homogeneous harmonic polynomials include into this space, and their literal sphere L2 image has no greater dimension. Thus the genuinely constructed degree-l harmonic L2 space has dimension at most (l+1)^3. No dimension estimate is supplied as a premise. This sufficient polynomial bound is not the sharper exact 2l+1 formula.

Status: author PASS; frozen pending root full-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `964a6697a5c2dda156c898dc80ebdfefe7a812a9d430fe3e292f53666e7b3c9b`. Independent log `lean/logs/SphereHarmonicDimension-root-audit.log`, SHA256 `aee8bdf435f5cfa429fc9c648883c2cb044e443db88cd05c6ccdf29a818a311f`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
