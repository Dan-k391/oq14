# Actual concentric material-cell geometry

Source: `lean/RadialMaterialCells.lean`.

SHA256: `29EB8E6E570F3073C681DF9FF4CAAC4B11BB5F096F76BB26B6ABC54263C99C14`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All eighteen exported theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The emitted object is 370872 bytes. Exact compiler output: `lean/RadialMaterialCells.final.log`, SHA256 `99E8236E8CF3F762B536567F1A3433C34B3C509F4D3864E91FA2937E5A184F94`. Root's independent full-source mathematical audit passed at this exact hash; independent compiler rechecks are in progress. The source is frozen. The pinned missing Mathlib.Analysis.NormedSpace.Connected dependency was built successfully; its log is `lean/RadialMaterialCells.library-build.log`. No shared configuration or frozen source was edited.

The cells are actual Euclidean balls, radial open annuli, and radial open exteriors. The ambient real module's actual rank is three. The genuine connected-sphere theorem therefore applies. The actual continuous map from unit sphere times a positive real interval, sending a pair to radius times direction, has image exactly the corresponding norm interval: the inverse witness uses the original point divided by its actual norm. Consequently the actual annuli and exteriors are preconnected. Inner balls are convex. Their openness follows directly from continuity of the actual norm.

The actual Euclidean Haar volume of every interface sphere is zero. For adjacent radii a less than r less than b, an explicit positive bridge radius is half the minimum of the two radial gaps. The bridge is the actual Euclidean open ball of that radius centered at r times the first coordinate basis vector. The triangle inequalities put its points strictly between a and b in norm. Off the single null interface sphere, every such point lies in one of the two adjacent annuli. The bridge ball is genuinely connected, and explicit points at radii r minus half the bridge radius and r plus half the bridge radius prove both overlaps nonempty.

Subset enlargement gives actual inner-ball/annulus, annulus/exterior, and inner-ball/exterior bridges. No connectivity, null-interface, bridge, AE coverage, or nonempty-overlap conclusion is assumed. This file supplies the continuous concentric geometry. Finite indexing, finite radial cell coverage and graph reachability are owned separately by `FiniteRadialPartition.lean`. No statement about arbitrary material geometries is claimed.
