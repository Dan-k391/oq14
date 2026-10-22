# Independent audit of common bounded radial families

Source: `lean/RadialPairedFamily.lean`.
SHA256: `66D2DD297F1993A612024BAB47434C8AF77478B11568361BED8A7DC885A4CAAC`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Exit 0, no warnings, and all sixteen reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/RadialPairedFamily-independent-continuation.log`.

The actual finite stack family is defined as the literal physical layers
when R>0 and its fixed total width is at most R; at other radii it is empty.
The actual Chain, outer radius at most 2R for R>=0, and fixed total-width
bound are derived. The family is proved eventually equal to the actual
literal stack. Parameter constraints are inherited from the actual segment
list. The gamma family therefore retains the already proved actual limits.

For the displayed quarter-wave lists the exact width and layer parameter
constraints are proved. Substituting sigma=1 and sigma=q^2 into the actual
parity limits derives the four displayed TE/TM-labelled scalar radial gamma
limits, with q positive. No coefficient or gamma limit is a premise.

Scope: fixed finite pair count and each fixed degree on the actual common
radius sequence. The small-radius trimming is explicit and does not change
the eventual literal stack. The TE/TM names here specify radial parameter
choices; spatial Maxwell reconstruction, uniform all-degree kernel bounds,
and identification of the complete finite-stack Green field remain separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 16 reports using only standard foundations. Final source SHA256 `66d2dd297f1993a612024bab47434c8af77478b11568361bed8a7dc885a4caac`. Independent log: `lean/logs/RadialPairedFamily-independent-continuation.log`; log SHA256 `7fda0c964b148a1d22e0c64b51ded2219ca1d13a37adf7bfa32bf2aeaa4728a0`. This certifies the stated scope, not either complete OQ14 construction.
