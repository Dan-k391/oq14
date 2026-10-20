# Actual electric cutoff control

`lean/WeakPoynting/ElectricControl.lean` is frozen at SHA-256
`0b6231a79a533074da3faef852f724c740d26952d69cf0b7d2f9b14d7e64add4`.
Eight selected exports directly compile without warnings and use only
`propext`, `Classical.choice`, and `Quot.sound`. Complete output and source
hashes are in `electric-control-verification.txt` and
`electric-control-provenance.json`.

The module proves the exact equality between regional L2 component norm
squares and physical integrated energy. It also identifies the energy of
actual zero-extended cutoffs with the corresponding weighted regional
integral.

For genuine regional weak Maxwell fields, positive real permittivity
`epsilon >= m > 0`, a real interior cutoff `zeta` with `|zeta| <= 1` and
`|gradient zeta|² <= d²`, and an outer cutoff `chi = 1` on its support, the
proved Caccioppoli identity yields

```
norm (zeta E) <= sqrt(3 (2 + 4 d² / (omega² m)) / m) * norm (chi H).
```

Both norms are the actual finite-component Pi norms of whole-space L2
zero extensions. The factor three is derived from comparison with the sum
of component norm squares. All integral inequalities use established
integrability and almost-everywhere coefficient positivity. No derivative
of permittivity is required.

The coordinator's independent full source review passed.
