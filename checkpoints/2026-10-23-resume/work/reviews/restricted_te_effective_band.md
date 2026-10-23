# Removing inactive TE coefficients

Frozen source: lean/RestrictedTEEffectiveBand.lean, SHA256 8805D24EFFBD0E2A87313826B1AD995DACB0CC280C6FD2386ED347EA107BEBBC.
Author final pinned compiler/object PASS: exit 0, no warnings, six standard-only reports. Log: lean/logs/RestrictedTEEffectiveBand-final.log. Independent audit pending.

Actual odd-degree projected columns vanish, and the degree-zero toroidal column vanishes by its actual polynomial derivative. Filtering to even degrees at least two therefore preserves the literal incoming amplitude, actual physical L2 input, and actual field jets; its support is a subset of the original finite support. This derives effective support, rather than assuming a band condition or replacing the physical norm. No named spherical-harmonic even-m basis equivalence is asserted.
