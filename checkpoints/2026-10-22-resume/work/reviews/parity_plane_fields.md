# Actual parity density fields and material strip representative

Frozen source: lean/ParityPlaneFields.lean.
SHA256: 2F64F9DC8AF196B9220C4CF9256CE72343B724F5B185236F61BD7E8D8685A5B2.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all twelve reports standard-only. Log: lean/logs/ParityPlaneFields-final.log.
Independent audit pending.

Electric and magnetic parity fields are literal density integrals of the
actual global point Maxwell parity fields. Their integrands are genuinely
integrable, and the fields are globally continuous with entry bounds
entryBound(k)*sourceMass. On the measurement plane the true electric parity
field has exactly zero tangential E, and the false parity field has exactly
zero tangential H. These are identities for the actual density integrals,
with no smooth source or limiting dipole assumption.

The total electric and magnetic continuous strip fields use the actual
ordinary free-volume fields plus both actual gain-weighted parity density
fields and the supplied incident field. The electric density term is
definitionally ParityMaterialField.reaction. NewtonStripMaxwell proves that
the continuous total electric field equals ParityMaterialField.total almost
everywhere on the genuine source-free strip, and both total fields are
continuous there for continuous incident data. This avoids restricting a 3D
AE equality to a 2D plane. No pointwise equality for an arbitrary L2
representative on that plane is claimed.

The magnetic density fields use the genuine magnetic point kernels already
proved to satisfy Maxwell. Interchange of their density integral with curl,
and the weak PDE characterization of the complete strip pair, are not claimed
by this file. Whole-plane coherent flux estimates and identification with a
physical finite radial stack remain separate constructions.
