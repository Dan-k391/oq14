# Exact complete parity material plane flux decomposition

Frozen source: lean/ParityTotalFlux.lean.
SHA256: F095A9307085FEC9F3F3107C184F0550A8769F212E93B2EEB023A7CE994DE1F0.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all two reports standard-only. Log: lean/logs/ParityTotalFlux-final.log.
Independent audit pending.

The literal total plane flux uses the complete gained parity electric and
magnetic density fields and an actual finite pure electric-wall incident
Maxwell pair. The free flux retains the same incident pair and actual free
volume fields. Exact plane selectors prove that the free flux is exactly
the actual free-E/incident-H mixed flux plus the free-volume quadratic flux.
The total flux is exactly this free flux plus four genuine reaction terms:
gained free-E/true-parity-H, false-parity-E/incident-H,
false-parity-E/free-H and false-parity-E/true-parity-H. The correct conjugated
magnetic gain is retained. The largest direct gained incident term is exactly
zero because the actual electric-wall incident tangential E vanishes.

The electric total used here is the continuous source-free-strip
representative of ParityMaterialField.total, as proved in ParityPlaneFields.
The magnetic field is defined from the genuine magnetic point density
partners; density/curl interchange and the full weak PDE of this pair are
not asserted by this algebra file. It also does not identify a physical
finite radial-stack Green field, construct Gram coefficients or normalize
physical incoming power.
