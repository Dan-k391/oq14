# Genuine finite scalar edge-jet interpolation

Frozen source: lean/EdgeScalarInterpolation.lean.
SHA256: 775B96DE7F51520B3938B753C1E4D7E0CCEBDD515AA0DA073ECA5893E1256EB3.
Author final pinned compiler/object PASS: exit 0, no warnings, three reports
using standard foundations only. Log: lean/logs/EdgeScalarInterpolation-final.log.
Independent audit pending.

The actual cosine/sine vector of scalar values and six tangential two-jet
components at edge points (r,y_j,0), with r nonzero and distinct y_j, spans
the entire finite jet space when real frequencies range over any nonempty
open rectangle. The proof represents every actual linear functional in its
canonical coordinate basis, invokes the derived EdgeCosineJets independence,
and obtains the full span from the actual zero dual annihilator. A finitely
supported frequency-coefficient witness is then constructed for every target
jet vector. No jet-surjectivity or coefficient-invertibility assumption is
present. This is the edge geometry used in the channel construction, not
an arbitrary planar point theorem.

The vector formulas will be identified with literal SymmetricScalarWaves
Frechet derivatives separately; those waves already satisfy actual Helmholtz
and TE Maxwell. Smooth angular approximation, actual finite even-TE-band
realization and physical incoming-power normalization remain open, so this
module alone is not a finite-power interpolation or channel theorem.
