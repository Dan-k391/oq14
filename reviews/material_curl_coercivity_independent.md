# MaterialCurlCoercivity — independent root audit

PASS. Fresh pinned Lean 4.19.0 source check, exit 0, 2 qualified standard-only axiom reports, no compiler warnings or errors. Uses existing dependency objects; not a clean aggregate build.

Log: `lean/logs/MaterialCurlCoercivity-root-audit.log`.
Source SHA256: `97fb8992be1e9f88d0682b7121ac1548e0e691598f3867d59d3bb9c10acf9604`.
Log SHA256: `fe39b623caae38c1fa97489acb6dd5ecc2dd5663ce8ad8397b103093bff919a9`.

Full frozen source read. The actual Maxwell curl identity identifies inverse-dielectric magnetic curl energy with k^2 times electric dielectric energy. The existing weak-energy Caccioppoli estimate then yields the localized weighted curl estimate with explicit constants. Actual coefficient bounds give subregion coercivity. These are energy estimates, not one-sided sup estimates or attained maxima.
