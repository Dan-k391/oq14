# Original-target and formal-coverage scope audit

Reviewer: continuation_review_sol. Date: 2026-10-20. Read-only audit of the
mathematical sources; only this review file was written.

## Available evidence and limitation

The requested original manual
`C:/Users/Daniel/Downloads/OQ14_Agent_Manual.txt` is currently absent.
Filename searches of Downloads and the workspace, including ignored tmp and
sources files, found no replacement. `evidence/input-manifest.json` records
that a 21,059-byte file with SHA256
`7a997ff52578392801d45d578d7f48ca5a00c8c60ba6533b838c818cd2ab8f96`
was present at the earlier input audit. That historical hash does not supply
its contents, so an exact comparison against every instruction or qualifier
in that manual cannot currently be certified.

The actual cached tutorial source is available at
`sources/cache/tutorial.txt`, SHA256
`5AA395227E49CE019A0E35F276F9B48298C2FBDA6EF07A9AABA6E5CCFB9E1879`.
Its Section 5.6, lines 4608--4673, was read directly. The relevant manuscript
sources `problem.tex`, `channel_unrestricted.tex`, the modal-packing theorem
in `modal_spectral.tex`, README, CLAIMS, and the formal-coverage boundary in
`lean/README.md` were also inspected. This is a scope comparison, not a fresh
mathematical validation of the complete written constructions.

Exact supporting locations and source hashes at this audit:

- `sources/cache/tutorial.txt:4619`: mode-volume definition and subsequent
  open-cavity qualification; `:4663`: same-mode hotspot/channel distinction;
  `:4669`: the two qualitative conjectures; `:4673`: OQ14 itself.
- `manuscript/sections/problem.tex:3`: additional quantifiers acknowledged;
  `:5`, `:16`, `:21`, `:33`, `:41`, `:45`: material, scattering, counted-space,
  channel, exception-regime, and hotspot definitions. SHA256
  `08AA7D74A0C8C86D821DCD91EA7F1C6FBB2608BE090A1DAD74BEDD5843F85C34`.
- `manuscript/sections/channel_unrestricted.tex:10`: the counterexample
  theorem; `:125`: its scope remark. SHA256
  `3BA0A98962F0F0A4F4D3DC4F9E86CF2C6BF4A9F444C23A5B4744AFCF396FD298`.
- `manuscript/sections/modal_spectral.tex:416`: full modal theorem;
  `:436`: actual maxima in the plane patch; `:440`: N-dependent insertion
  contrast. SHA256
  `C51E80D87B541E718159011C96692A929BA6F1E981624DFBDE1AAB019A2F1364`.
- `manuscript/sections/hotspot_closure_audit.tex:32`: driven peak points need
  not lie in the plane; `manuscript/sections/channel_closure_audit.tex:320`:
  explicit formalization boundary.
- `lean/README.md:713`: explicit statement that formal verification is
  incomplete, followed by missing continuum steps. SHA256
  `050C0DC59825F21CB51DDC49AF40F6C4593387829F1B0427670A30A0141FED5A`.

## Original tutorial versus frozen manuscript target

The tutorial asks whether arbitrary finite numbers of subdiffractive electric
hotspots can be packed into arbitrarily small area by dielectric structuring,
and whether power-carrying orthogonal modes/channels remain diffraction
limited in a given area. Its preceding discussion emphasizes that many
hotspots in the same mode provide only one independent channel and that
distinct modes need wavelength-scale supporting structure. It describes
mode volume using electric energy divided by local electric energy density,
and expressly mentions quasinormal generalizations for open cavities.

The tutorial's prose does not fix a transmission threshold, a quantitative
passage condition, absolute bypass tolerance, output selection, or a rigorous
meaning of the given area. The manuscript acknowledges this explicitly at
the beginning of `problem.tex`: its frozen targets make additional choices
and are not quotations of an already quantified theorem.

For channels, the manuscript fixes an actual square D, real frequency,
common ordinary positive scalar dielectric bounds, compact finite-piece
devices with unrestricted support and feature scales, power-normalized
incoming/selected outgoing Hilbert spaces, and inequalities required for
every vector in the counted subspace. Passage is at least eta times selected
output power; absolute bypass is at most delta times incident power. The
square need not be a sole topological connection. The universal statement
over all permitted thresholds is indeed refuted by a counterexample in
one permitted parameter regime.

The written counterexample fixes any `0 < eta < delta`, any tau in (0,1),
frequency, material interval, and square, and constructs arbitrarily large
finite counted spaces with the complete scattering map selected as output.
Its edge flux circulates across the square boundary, with an exterior return
of the same limiting magnitude. This explains the strict bypass allowance.
The result does not settle delta <= eta, a required receiving hemisphere,
a sole-connection interpretation, or uniformly bounded material support.
It should therefore be described as a disproof of the explicitly quantified
manuscript assertion, without silently equating it to every possible
operational interpretation of the tutorial's broad channel question.

For hotspots, the written modal theorem is stronger than a driven-field
construction in several relevant respects: one actual outgoing quasinormal
mode has fixed real pole frequency, prescribed arbitrarily high Q, genuine
nonzero reciprocal residue normalization, and arbitrary finite numbers of
actual three-dimensional peaks whose maximizing points lie in the prescribed
plane patch. The same material interval is used for all N. Its insertion
contrast may depend on N, support is not uniformly bounded, and minimum
feature size and positive energy fraction per peak are not imposed.
The residue normalization must remain explicit: it is not the divergent
ordinary all-space positive energy of a radiating quasinormal mode.
The driven three-dimensional theorem has only a projection constraint for
peak locations, and must not be promoted to the stronger modal/common-plane
statement by relabeling.

## Formal completion boundary

The registered 2033-declaration aggregate and subsequent targeted module
checks are substantial foundational results. They do not yet constitute a
Lean proof of either full written device theorem. The new weak Helmholtz
continuation and regional Maxwell interface theorem prove genuine PDE
continuation, rather than assuming it. They still require actual material
bridge geometry and reachability to obtain global homogeneous uniqueness.

Even after global uniqueness is obtained for the construction's geometry,
full channel closure still requires the all-angular-order physical Green
limit, actual self-consistent inclusion response, whole-plane coherent flux
convergence, and physical power-normalized counted-space construction.
Full modal closure still requires the conical spectrum and coefficients,
Runge/rounding where used, reciprocal normalization, spectral branch and
infinite-degree modal isolation, and the final simultaneous peak construction.
An abstract theorem parameterized by those conclusions cannot count as their
formal proof. Completing only a restricted support/volume/angular-band regime
would not establish the unrestricted target.

Conclusion: the present continuation batch is a genuine, audited advance
toward the full requested formalization, and remains partial. The repository
currently states that boundary honestly. The unavailable manual is the one
remaining source-comparison limitation of this review.
