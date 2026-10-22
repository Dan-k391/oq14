# Actual finite sphere volume and interaction powers

Source: `lean/FiniteSphereScale.lean`.
SHA256: `C017C84F477CF6CD845F041C00389B515300DCCD1DDF8D703A77D1CE059CC5D2`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all six reports use only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/FiniteSphereScale-final.log`. Root independent complete-source mathematical review and pinned compiler also pass: exit 0, no warnings, standard-only reports. See the corresponding lean/logs/FiniteSphereScale-root-audit.log audit log.

The actual finite union of radius-rho*a balls has volume at most
cardinality*volumeConstant(rho)*a^3, without requiring separation for this
volume bound. Its square root has the corresponding actual a*sqrt(a) bound.
The genuine weighted trial sum has an O(sqrt(a)) norm bound when the actual
center component amplitudes are bounded by A/a.

The physical isolated polarization component is proved bounded by chi times
the incident component. Consequently the explicit actual finite cross-field
interaction sum is bounded by a fixed constant times a^2 for those center
amplitudes. This follows from the actual radius-cubed exterior Hessian bound;
no interaction convergence or operator bound is assumed.

Scope: fixed finite set, common shrinking radius, fixed separation parameter,
and constant trial polarizations. The actual inverse source errors and their
eventual small-radius family wrapper are subsequent steps.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `c017c84f477cf6cd845f041c00389b515300dccd1ddf8d703a77d1ce059cc5d2`. Independent log: `lean/logs/FiniteSphereScale-root-audit.log`; log SHA256 `87fb564c1fbb9b2abd8c02e67b10d5c8cc94cc231b1473a5a2cfcf156d781544`. This certifies the stated scope, not either complete OQ14 construction.
