# Actual density weak curl from derived differential bounds

Frozen source: lean/DensityWeak.lean.
SHA256: 7490773F178B17988B72F9E52ACFC9769E08723DDBF74D7D0A2750C871B51E1B.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all three reports standard-only. Log: lean/logs/DensityWeak-final.log.
Independent audit pending.

Actual density coordinate derivatives are bounded by the true source L1 mass
times the actual uniform point differential bound. Their measurable
representatives follow from mathlib's measurable Frechet derivative theorem;
the bound derives local integrability. Existing RadialInterface integration
by parts then proves the actual weak curl pairing against every compact C1
test. The proof requires neither C1 density assumptions nor an assumed weak
PDE. Generic actual point differentiability, source-variable differential
continuity, differential bounds and point curl identity remain explicit;
SphereParityDifferential and ParityDensityMaxwell provide the actual parity
kernel instances for the next assembly.

This freezes the integration-by-parts bridge. Concrete parity TestMaxwell
instantiation and combination with the actual free-volume equations to obtain
the complete material weak Maxwell pair have not yet been written. Physical
finite radial-stack Green reconstruction remains separate.
