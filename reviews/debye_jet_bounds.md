# Actual vector Maxwell derivative envelopes

`lean/DebyeJetBounds.lean` has seven selected reports. Author final compile
and object passed with exit0, no warnings, and standard foundations only.
Independent audit is pending.

The proof bounds genuine Frechet jets of each coordinate partial by the
next scalar derivative, bounds curls by two component derivatives, and
uses the actual coordinate product derivative bound for curl(x*f).
Two curls therefore control both regular Maxwell polarizations by scalar
jets through order N+2. Applied to the constructed normalized harmonic
representatives this gives a degree envelope with the same factorial
radial amplitude and degree power as the scalar envelope, with an explicit
larger compact derivative scale. It holds at the origin as well.

No vector series convergence or Green identification is assumed here.
Derivative order is finite and the required control radius depends on it.

Source SHA256:
`bac02f5b914fc8b4131aea05d95a005a883a27cc9dcece3f1725f5be5d593350`.
Final log `lean/logs/DebyeJetBounds-final.log` SHA256:
`1597020214d066735df186eb4c0c37368e8aab5dd76f2965dd7942cdb6eee8aa`.
