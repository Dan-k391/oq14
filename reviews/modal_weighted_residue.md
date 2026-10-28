# ModalWeightedResidue — author verification

Author PASS, 2026-10-28. Source `lean/ModalWeightedResidue.lean` SHA256 `7AFFF571F652E5B4C2690EB6DA6EB0B909D106567CB6B9D1BA7FE23F379EF88B`. Pinned final source/object compilation completed with exit 0, no diagnostics, and two standard-only reports.

Final log: `lean/logs/ModalWeightedResidue-author-final.log`, SHA256 `F68F3E4C70CA451F4EB163E9F713D1879503785AB1AEA15553C8F742BDF66CC2`. Exit receipt: `lean/logs/ModalWeightedResidue-author-final.exit.log` = 0. Independent audit pending.

The actual weighted global residue field equals its interior residue amplitude divided by I times the entire driven numerator datum. Equality is proved in physical L2 coordinates: inside the sphere the actual regular dipole expressions agree algebraically; outside, including the interface convention, the square-root susceptibility vanishes. This identity does not require a determinant root or simple derivative.

The kernel corollary still has the explicit positive-real volume identity premise inherited from the analytic continuation bridge. A separate endpoint can discharge it with `ModalDrivenRepresentation.volume_equation`. This module does not itself prove unconditional kernel membership or root existence.
