# Concrete disjoint-ball cells

Source: `lean/DisjointBallCells.lean`.

SHA256: `8527949A122B55F7462F2D2A728F2B1303C68528AD6718BD20C0EEFCB67C0C3E`.

Final compiler exit 0; importable object 301424 bytes; all eight selected theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`. Verbatim final output is in `lean/logs/disjoint-ball-cells-check.log`.

Cells are the literal open inclusion balls and their strict common exterior, indexed by `Option ι`. Their openness, preconnectedness, and AE volume cover are proved. Each inclusion has an actual connected open ball crossing its boundary and excluding all other closed inclusion balls. The proof gives explicit interior and exterior witnesses on one fixed unit direction. The cover of that bridge uses the actual null interface sphere. Every pair of cells is connected in the bridge graph through the common exterior. All strict separation and positive radius assumptions are explicit.

Status: root full-source audit and independent compiler PASS. Frozen at the hash above.
