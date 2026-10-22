# Actual finite-stack high-degree reaction estimate

Source: `lean/RadialHighOrderBound.lean`.

SHA256: `468B35C302A2C3C44112E949B6FB423058D62441586BCB5A0593562411949DA7`.

Author final compiler exit 0, no warnings; importable object 635544 bytes. All nine selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialHighOrderBound-final.log`.

The leading outgoing factorial coefficient times the actual regular origin coefficient is proved exactly equal to 1/(2l+1). For l>=2R, the actual barrier comparison gamma is at least l/2, the load quotient prefactor is at most four, and the regular Gaussian exponent is at most R/2. Actual outgoing and derivative estimates, the derived outgoing stack load bound, and regular positivity give

    norm(actual reaction gamma) * regular(l,s)^2
      <= 4 exp(3R/2) s^(2l+2) / ((2l+1) R^(2l+1)).

Here R>0, 0<s<=R, X>0, and every actual layer obeys q_g^2 b_g^2<=l(l+1). The coefficient is literally `RadialSource.gamma`, with the actual finite stack transfer and source construction. No reaction bound, regular positivity, series identification, or convergence is postulated.

This is a sufficient explicit high-degree estimate, not the sharpest possible manuscript constant. The companion tail source derives genuine convergence. Spatial Maxwell Green reconstruction and full all-order physical Green convergence are separate tasks.

Status: author PASS and root complete-source mathematical audit plus independent pinned compiler PASS (session 19990), exact hash unchanged; no warnings and all nine reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 9 reports using only standard foundations. Final source SHA256 `468b35c302a2c3c44112e949b6fb423058d62441586bcb5a0593562411949da7`. Independent log: `lean/logs/RadialHighOrderBound-root-audit.log`; log SHA256 `87b3e2acf79e727e389aa6668aa78eea3dec555db77236ebc7eecfddd022379c`. This certifies the stated scope, not either complete OQ14 construction.
