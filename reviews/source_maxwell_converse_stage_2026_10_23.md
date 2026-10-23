# Actual Maxwell source converse stage — October 23, 2026

The exact author compiler receipts and source hashes for fourteen root modules are
in `source_maxwell_converse_stage_2026_10_23.json`. These are targeted checks, not
a new clean aggregate release. Independent reviews are recorded separately in
`tmp/audited_after_5238.json` as they complete.

The general converse derives uniqueness for outgoing vacuum Maxwell fields from
actual weak flux conservation, the proved Rellich theorem, and weak continuation.
The outgoing trace package spells out the actual far-field limits, transverse
electric amplitude, spherical continuity and uniform bounds. Subtracting the
genuine compact-source Green response then proves that a locally square-integrable
forced field with that trace and exterior smoothness equals the volume response.

For the explicit finite layered source, all those analytical prerequisites are
derived. The literal layer-minus-vacuum field equals a regular solid Maxwell wave
in the core. Its regular value is used at the origin. Actual smooth-test localization
joins the regular near-origin equations with the punctured equations across every
layer. Products with punctured source fields are proved integrable using clipped
representatives on the test support. No integrability of a singular source field
at the origin is assumed.

The actual polarization is globally L2, integrable and compactly supported. The
corrected fields are locally L2, have the derived outgoing trace, and are smooth
beyond the outer interface. `SourceVolumeRepresentation.actual_response` therefore
identifies the explicit correction with the actual electric and magnetic volume
responses using only genuine layer data, the physical TM dispersion relation,
and polynomial homogeneity/harmonicity. It has no caller-supplied Maxwell,
radiation, regularity, response-identification or uniqueness premise.

`MaterialVolumeConverse` supplies the subsequent algebraic step from actual spatial
weighted fields to the material volume equation. Its explicit premises are not yet
the final assembled physical theorem: the matching susceptibility, weighted radial
data and invertibility must be instantiated by the construction. The TE source
analogue, complete tensor reaction assembly, modal pole isolation/residue/maxima,
fixed finite-power rounded hotspots and complete channel theorem remain separate
unfinished obligations. This stage is not full OQ14 closure.
