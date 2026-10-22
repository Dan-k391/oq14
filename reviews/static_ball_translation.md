# Actual translation of the uniform-ball weak Hessian

Source: `lean/StaticBallTranslation.lean`.
SHA256: `D1C10524321A21FC650A257E62A834AC2A1BCEF0448E18692FF8D649767F7F50`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all eight reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticBallTranslation-final.log`.
Root independent full-source mathematical and fresh pinned compiler review
PASS at this exact hash, no warnings and all eight reports standard-only.
Independent log: `lean/logs/StaticBallTranslation-root-audit-final.log`.

The actual scalar L2 translation is composition with x-c under actual
measure-preserving addition. Its representatives and bilinear Schwartz
pairings are proved using the actual change of variables. The translated
ball indicator is identified with the actual ball centered at c, and the
translated Hessian representative with the explicit formula at x-c.

The proved translated Schwartz derivative pairings feed the generic actual
Fourier weak-derivative theorem. Linearity translates the genuine Hessian
trace, and pointwise symmetry is retained. The same proved algebraic
symmetry/trace argument determines the translated Hessian's Fourier symbol.
No Newton translation covariance, arbitrary-center depolarization identity,
or conclusion about a Green operator is assumed.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `d1c10524321a21fc650a257e62a834ac2a1bcef0448e18692ff8d649767f7f50`. Independent log: `lean/logs/StaticBallTranslation-root-audit-final.log`; log SHA256 `dd123cd71c0001b01a9ef77c5adccae54c3b81096014d0485b3606c2dedad39b`. This certifies the stated scope, not either complete OQ14 construction.
