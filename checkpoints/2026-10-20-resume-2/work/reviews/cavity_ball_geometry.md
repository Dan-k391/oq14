# Bounded cavity connectivity

Source: `lean/CavityBallGeometry.lean`.

SHA256: `77A74BB0C6B48A6456C8AD322D7BB47B621E73A6045275C87085A8E2135A81F6`.

Final compiler exit 0; importable object 460240 bytes; all 13 selected theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Verbatim final output: `lean/logs/cavity-ball-geometry-check.log`.

The literal cavity is an open concentric core ball intersected with the strict exterior of a finite family of strictly separated inclusion balls. Every closed inclusion ball is strictly contained in the core. Connectivity is proved by an explicit globally continuous inward clamp of full punctured-space paths into a smaller ball, avoiding every center and fixing the endpoints, followed by the actual finite radial push from `DisjointBallGeometry`. The inflation is chosen to remain strictly inside the core. This derives actual path connectivity, connectivity, openness, and nonemptiness without a topology premise equivalent to the conclusion.

Status: root full-source audit and independent compiler PASS. Frozen at the hash above.
