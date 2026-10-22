# Actual homogeneous angular integration identities

Source: `lean/AngularPolynomialMean.lean`.
SHA256: `8A2C67728F5AC7215EFE199DDFA8B059BD819343ED2E5B0B4DF0067E5D8AC3E3`.

Author target plus importable object compiler exit 0, no warnings. Object 597104 bytes. Twelve selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/AngularPolynomialMean-final.log`. Forbidden-token scan passed.

The mean is the literal real integral of the actual polynomial restriction against the genuine sphere measure, constructed as an actual linear map using actual integrability of continuous restrictions. Multiplication by any radius-squared power leaves this integral unchanged on the unit sphere. Nonzero-degree homogeneous harmonic means vanish by the actual cross-degree integral result.

For every actual homogeneous degree-d polynomial p, genuine finite Fischer span induction proves mean(Delta p)=d(d+1)mean(p). On each actual radial Fischer generator the exact formal Laplacian coefficient is already derived; only its harmonic degree-zero part can survive the actual mean, and the coefficient then equals d(d+1). Zero and low degrees are included.

A second actual Fischer induction proves mean(partial_i p)=(d+2)mean(X_i p). For a harmonic generator h this follows from the preceding Laplacian identity applied to X_i h and the exact product derivative. The only possibly nonzero pairing with X_i has harmonic degree one, where the numerical factor is exactly three. The derivative of each radius power supplies the remaining 2j term. These are genuine polynomial integration-by-parts identities with no spherical Green, spectral normalization, test-separation or derivative conclusion assumed.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 12 reports use only standard foundations. Final source SHA256 `8a2c67728f5ac7215efe199ddfa8b059bd819343ed2e5b0b4df0067e5d8ac3e3`. Independent log `lean/logs/AngularPolynomialMean-root-audit.log`, SHA256 `808c9eb589014d86776eb5e9a837d97479af8ad0546b0d6768919058f3e839b4`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
