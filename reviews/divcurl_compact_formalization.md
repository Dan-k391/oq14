# Compact weak div–curl approximation

`lean/WeakPoynting/DivCurlCompact.lean` is frozen at SHA-256 `317b3b2169b77f2954ef02a474c47687b3ccca38f2ffe593ec14155271923a13`. The complete direct build exited zero and produced seven selected axiom reports, each using only `propext`, `Classical.choice`, and `Quot.sound`. Evidence is `divcurl-compact-verification.txt` and `divcurl-compact-provenance.json` alongside the source.

The module defines weak divergence and weak coordinate derivatives by genuine compact C1 test identities in actual L2 classes. Its main approximation theorem derives simultaneous strong L2 approximation of the field, curl, and divergence by actual Schwartz fields. The approximants are compactly supported smooth convolutions of the field, not postulated approximating objects. Compact support is imposed on a representative of each input L2 component; the curl and divergence need not separately be supplied with compact-support representatives.

Curl and divergence commutation follow from reflected actual kernel tests. The minus sign in the reflected derivative is explicitly proved. The final two lemmas derive the weak partial identity for actual Schwartz derivatives by integration by parts and show that this identity passes to strong L2 limits through the actual continuous test pairings.

The checkpoint's three compiler errors were resolved on resumption. This module does not itself claim existence of all weak derivatives; that construction is in the separate `DivCurlRegularity.lean` module. No source pins or shared build configuration were changed.
