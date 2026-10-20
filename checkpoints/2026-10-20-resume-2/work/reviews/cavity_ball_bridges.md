# Cavity interface bridges

Source: `lean/CavityBallBridges.lean`.

SHA256: `FCDDD221C1FE8FCAB5372FB173019C4A1C75453947E75D56686DE64C89E20B6D`.

Final compiler exit 0; importable object 305792 bytes; all three selected theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact final output: `lean/logs/cavity-ball-bridges-check.log`.

The first actual bridge joins each inclusion interior to the literal bounded cavity. A boundary point belongs to the open core and avoids every other closed inclusion; a sufficiently small explicit ball remains in that open region. The bridge crosses the chosen inclusion sphere with explicit inward and outward points. The second bridge crosses the core boundary between cavity and enclosing annular shell; strict containment of all inclusions leaves an actual neighborhood of the boundary point obstacle free. Both AE covers use actual zero-volume spheres, with no assumed interface propagation or connectivity.

Status: compiled and ready for independent root full-source audit; held unchanged pending audit.
