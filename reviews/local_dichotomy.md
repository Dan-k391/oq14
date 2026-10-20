# Connected propagation of a local unit dichotomy

Source: `lean/LocalDichotomy.lean`.

SHA256: `2BB9325FA8F1D0421528F3D77BB5C0BE5E6F1D72526E991CA69743F422BF65E0`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All three exports report only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full-source audit passed at this exact hash. The source is frozen.

Suppose every point has either a neighborhood disjoint from a set or a punctured neighborhood contained in it. The closure of that set is open: at a closure point the disjoint-neighborhood branch contradicts frequent membership, and the punctured branch supplies a neighborhood inside the closure. The closure is also closed. On a preconnected space, one actual member therefore makes the set dense, and excludes the disjoint-neighborhood branch at every point. This proves punctured membership globally, with no global determinant hypothesis.
