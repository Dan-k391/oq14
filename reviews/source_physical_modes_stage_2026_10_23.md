# Actual physical TM and TE source modes

Root author review, October 23, 2026. Exact source and successful compiler-log
hashes for twelve root modules are frozen in
`source_physical_modes_stage_2026_10_23.json`. Every listed report uses only
`propext`, `Classical.choice` and `Quot.sound`. Independent reviews and their
fresh compiler checks are registered separately in `tmp/audited_after_5238.json`.

The TM result `SourceTMPhysicalResponse.core_integral` now identifies the
actual material inverse applied to the weighted vacuum source mode with the
constructed layered source field, then evaluates its literal Green integral
throughout the open vacuum core, including the origin. Material susceptibility,
its finite radial partition and positive-frequency invertibility are constructed
from the supplied finite chain and physical bounds. Maxwell equations, local L2,
compact polarization, exterior smoothness and outgoing traces are proved for
the actual fields; they are not hypotheses of the final physical result.

The TE counterpart `SourceTEPhysicalResponse.core_integral` has the same actual
inverse and core-integral conclusion. The radial representation uses sigma=1,
with physical dielectric q-squared/sigma. Its source integrability and compact
support are derived in `SourceMuBounds`; the temporary integrability parameter
of the punctured helper is discharged in `SourceTEGlobal.forced_maxwell`.
The actual finite partition and invertibility come from `SourceMuMaterial`.

The core multiplier is gamma+I. TM multiplies the regular electric field; TE
multiplies the regular magnetic profile. In the normalized free-source dyadic
assembly the physical reaction coefficient has the separate sign -(gamma+I).
This sign must be checked when the source coefficients are assembled.

These are complete single-mode identifications for the stated finite radial
stacks at unit frequency. The full tensor source-mode series and its spatial
derivatives still require assembly and convergence identification. This stage
does not prove the final unrestricted channel or modal hotspot theorem, nor
constitute a new combined clean release. Release5238 remains immutable.
