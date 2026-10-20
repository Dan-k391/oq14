# Cap angular shooting

Author verification for `lean/CapAngularShooting.lean`.

- Source SHA256: `81D5005801C73454FC340C5B9CC38CB6A46059D281ABC75654E305C7E57B00A0`.
- Pinned Lean 4.19.0 `lake env lean -o .lake/build/lib/lean/CapAngularShooting.olean CapAngularShooting.lean`: exit 0, no warnings; object 372288 bytes.
- Exact log: `lean/CapAngularShooting.final.log`, SHA256 `FB6567BE95F62278B13F33736CD703D5CB59FF3AC0E90EFC9EDB4D46E4DBCA51`.
- All seventeen theorem dependency reports contain only `propext`, `Classical.choice`, `Quot.sound`.

The determinant is built from the actual regular-pole and odd Legendre series and their proved actual derivatives. It is continuous in the parameter on `[0,2]`. At zero it is `-F'_0(t)<0`; at two it is exactly `d*t>0`. The intermediate value theorem therefore constructs an actual root strictly between zero and two for every `d>0` and `0<t<1`. The square-root expression constructs an actual exponent strictly between zero and one and proves its literal quadratic relation to the root.

The displayed interior and exterior functions are scaled actual series. Their first and second derivatives and actual Legendre equations follow from the already proved series calculus. Their values match identically; the determinant root gives the literal weighted flux matching. The outer function's value at the pole is the positive number `F_a(t)`, so the constructed matched solution is nonzero without a nonvanishing premise.

Independent root full-source and compiler audits requested. Frozen source. Scope: an actual matching root and actual one-dimensional matched solutions. No weak eigenfunction on the sphere or sphere H1 assertion is made here.

## Independent root verification on resumption

Full source reviewed and pinned Lean compiler returned exit0. All 17 selected reports use only the standard foundations. Source SHA256 `81d5005801c73454fc340c5b9cc38cb6a46059d281abc75654e305c7e57b00a0`. Independent log: `lean/logs/CapAngularShooting-independent-root.log`. Actual definitions and hypotheses were checked; this result does not close the outstanding full Maxwell/OQ14 constructions.
