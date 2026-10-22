# Actual radial boundary selection

Source: `lean/RadialBoundarySelection.lean`.
SHA256: `59D329D7F65C42A86B9EEF9525C97F80941BFDFAE6D4D13214DC1A96C046DCB6`.

Author target plus importable object compiler exit 0, no warnings. Object 267048 bytes. Four selected reports standard-only. Log: `lean/logs/RadialBoundarySelection-final.log`. Forbidden-token scan passed.

For the literal Riccati-Hankel functions, an actual scaled combination limit A forces its incoming coefficient to vanish and fixes its outgoing coefficient by a*(-I)^(l+1)=A. The proof subtracts the actual outgoing/incoming asymptotic errors and uses the already proved half-period nonconvergence argument; no radiation selection is assumed. Given actual first and second Riccati ODE derivatives, the genuine variation-of-coefficients theorem supplies the expansion, after which this limit selects the literal outgoing function.

The generic two-solution variation proof is also established on any actual open preconnected real set by differentiating the literal Wronskian quotient coefficients and proving they have derivative zero. Specializing the actual Hankel Wronskian gives the expansion on finite positive-radius intervals. ODE derivatives and scaled limits are explicit premises of these generic supporting results; they are discharged for the actual Green moments separately. No source normalization or PDE identification is inferred by this generic file.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 4 reports use only standard foundations. Final source SHA256 `59d329d7f65c42a86b9eef9525c97f80941bfdfae6d4d13214dc1a96c046dcb6`. Independent log `lean/logs/RadialBoundarySelection-root-audit.log`, SHA256 `19ad87c16a35462329714051c724dba3ab7a5cf28193ce5838386c8166548e24`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
