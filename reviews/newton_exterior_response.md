# Actual exterior Newton and electric source integrals

Frozen source: `lean/NewtonExteriorResponse.lean`.

SHA256: `AF89D26AC92DA283820E20024B821CFAAD9CB4B98F5D9C78142E9125AC1D98AD`.

Pinned Lean 4.19 source compilation and direct olean emission passed on 2026-10-20. All 15 exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The central-ball cutoff of the ordinary Newton Hessian is locally integrable. For a compact L1 source, compact tests separated from the source remove the cutoff exactly, and the previously proved weak-Hessian translation identity gives the ordinary kernel pairing. Its local L2 realization supplies actual local integrability. Separation by compact smooth tests on an open exterior region then identifies the actual bounded Newton operator there.

The main result `newton_ae_exterior` gives equality almost everywhere for `norm x > R`, with source support in the ball of radius `S` and `S < R`. `source_integrand_integrable` proves genuine integrability at every source-separated observation point. `electric_ae_exterior` combines the static and dynamic terms into the ordinary outgoing dyadic source integral.

The result identifies equivalence classes almost everywhere. Continuity of the ordinary exterior representative, needed for pointwise radiation limits, is subsequent work. No path-limit conclusion follows from an almost-everywhere equality alone.

Independent full-source reviews by the root and the modal agent both passed. Both checked the source/test separation, actual local integrability before test separation, coordinate symmetry, and exact combination of the independently integrable static and dynamic source integrals.
