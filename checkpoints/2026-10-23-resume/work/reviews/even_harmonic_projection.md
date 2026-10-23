# Actual even-degree harmonic symmetry projection

Frozen source: lean/EvenHarmonicProjection.lean.
SHA256: 09CB4BA60397D4E5D68754821960D4D656069DB59250B480A545EC3345C7C61E.
Author final pinned compiler/object PASS: exit 0, no warnings, seven reports
using standard foundations only. Log: lean/logs/EvenHarmonicProjection-final.log.
Independent audit pending.

The literal polynomial projector discards odd degrees and averages each even
homogeneous harmonic polynomial under the genuine half-turn. Homogeneity and
harmonicity are preserved. Its polynomial evaluation is exactly invariant
under the half-turn, central inversion, and equatorial reflection. The actual
regular scalar wave constructed from that polynomial has the corresponding
half-turn and central symmetries, with its real radial factor unchanged by
actual norm preservation. These are the geometric symmetries encoding the
manuscript's even-degree, even-azimuthal sector; no coefficient or m-basis
identification is assumed. Actual TE Maxwell wall conversion is supplied by
the separate HalfTurnMaxwellParity module. Jet interpolation and physical
incoming power remain separate conclusions to construct.
