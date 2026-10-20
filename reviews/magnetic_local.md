# Actual local L2 magnetic response

Frozen source: `lean/MagneticLocal.lean`.

SHA256: `CB712FAF80404E7A4242169045BEAEE12CFC8D5BB31E54762E4E3E55C0E06881`.

The pinned Lean 4.19 compiler and direct olean emission completed successfully on 2026-10-20. All three exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The actual outgoing scalar-kernel gradient is locally integrable. The proved exact-cutoff convolution theorem therefore gives local L2 for each of its compact-source convolution components. Their actual curl combination with factor `-i*k` is precisely `MagneticResponse.magnetic`, which consequently belongs to L2 on every observation ball and is locally integrable.

Root and hotspots independently read the full source and accepted the field definition, component order, factor, and actual spatial regularity. The scattered magnetic field is not assumed to satisfy an energy bound or a weak equation; this module establishes its regularity, while the separate source module proves its equations.
