# Actual radial TE magnetic trace

Frozen source: lean/RegularTEMagneticTrace.lean, SHA256 DBD4BA6F6B1D80D5A97A06C88DBA5CD077378D1037DA6D083C8729C6CBE2E51A.
Author final pinned compiler/object PASS: exit 0, no warnings, four standard-only reports. Log: lean/logs/RegularTEMagneticTrace-final.log. Independent audit pending.

For every actual homogeneous harmonic polynomial and incoming/outgoing TE component, the actual radial magnetic trace on radius r is exactly -I*l*(l+1)*radial(r)*p(n)/(2*r²). It is derived from the previously proved Riccati radial curl formula and actual homogeneity; no trace is assumed. Actual phase norm one and the genuine Hankel polynomial limits imply eventual bounds of two for both radial values and derivatives. These bounds are scalar, uniform in angle, and for fixed degree; this module does not claim a uniform bound over all angular degrees or a whole-plane flux theorem.
