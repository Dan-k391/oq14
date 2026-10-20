# Actual material fields with continuous exterior representatives

Frozen source: `lean/ExteriorMaterial.lean`.

SHA256: `DF8A9D46DD43B4A751DE3E4036F616058B0A3793139971C8CB8E9F6E8C192982`.

Pinned Lean 4.19 direct source compilation and olean emission passed on 2026-10-20. All nine exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The actual scattered electric field is replaced outside its source ball by the continuous ordinary dyadic integral. The replacement is globally equal almost everywhere to the previous volume response. Local L2 regularity, compact smooth-test Maxwell equations, and the exact material relation transfer through proved integral congruence.

The existence theorem uses the already derived inverse under `252 * bound * k^2 * R^2 < 1`. It retains the numerical norm bound, actual source self-consistency and locally square-integrable total fields. Its scattered electric representative is continuous at every point outside the source ball and equals the literal dyadic integral there.

The module does not assert a radiation estimate, arbitrary-size invertibility, or pointwise global Maxwell regularity.

Independent full-source reviews by the modal agent and the root both passed.
