# Independent Sol audit of actual Maxwell exterior vanishing

Source: `lean/MaxwellExteriorRellich.lean`.

Audited SHA256: `44AE2A32999B21289CDD2E8A4E24EA66B07A32D3D2E5BA9AA84CF95B9AC46A28`.

Independent full-source mathematical audit: PASS. Independent pinned Lean 4.19 compilation: exit 0, no warnings, five dependency reports containing only `propext`, `Classical.choice`, and `Quot.sound`, on 2026-10-20. The frozen source was not edited.

For each actual electric and magnetic component of the compact-source fields, the literal exterior field is smooth and satisfies the actual scalar Helmholtz equation. The proved far-power and angular-energy results give decay of its actual spherical mass. The genuine scalar exterior Rellich theorem therefore supplies pointwise zero for every component throughout the actual exterior, and finite coordinate extensionality reconstructs vector-field vanishing.

For a homogeneous physical volume-block solution, the proved homogeneous volume power identity gives zero actual far power of its literal material source. Actual source integrability and support, and the exact exterior equality of the chosen electric representative, then produce both exterior-zero conclusions. Finally their actual supports lie in the prescribed closed ball: any support point outside would contradict pointwise exterior vanishing. Taking the topological support closure inside the closed ball yields genuine compact support of both physical field representatives.

The hypotheses contain the actual physical homogeneous volume equation and material support, rather than outgoing uniqueness or compact support of the fields. No Rellich, field-equation, far-power, or exterior-zero conclusion is inserted as a premise.
