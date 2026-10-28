# ComplexMagneticAnalytic — independent root audit

PASS. Fresh pinned Lean 4.19.0 source check, exit 0, 4 qualified standard-only axiom reports, no compiler warnings or errors. Uses existing dependency objects; not a clean aggregate build.

Log: `lean/logs/ComplexMagneticAnalytic-root-audit.log`.
Source SHA256: `ab1e4062b345328c7971e9c6438e984813b41786d1eebe1b111327a819de57bf`.
Log SHA256: `1079ce554c3f88cb5653c03c9fc03d70794043266b241f08b0e7312ecbe96917`.

Full source read. The static singular gradient is subtracted before the parameter-analytic L2 construction. The exact complex-frequency derivative has no spatial singularity beyond a bounded direction factor, and compact uniform derivative bounds establish actual L2 analyticity. No singular full-gradient L2 claim is made.
