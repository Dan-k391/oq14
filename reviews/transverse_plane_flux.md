# Exact transverse plane cancellation

Frozen source: lean/TransversePlaneFlux.lean, SHA256 89D4A1248F98B236EC964FADC2EA75EAD3BF081C6BD321633C25AC0007F95BA2.
Author final pinned compiler/object PASS: exit 0, no warnings, three standard-only reports. Log: lean/logs/TransversePlaneFlux-final.log. Independent audit pending.

The actual triple-cross projection onto the transverse directions differs from a vector by exactly its radial component. The actual source leading electric field has zero normal plane cross product with that projected magnetic field. This is a literal algebraic identity using the previously proved source radiation identity and the zero plane coordinate; no flux cancellation is supplied as a hypothesis. Actual direction normalization also gives a componentwise projection error bound from the radial dot product.
