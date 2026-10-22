# Actual local volume-response/Herglotz coherent flux

Frozen source: lean/SourceHerglotzLocal.lean.
SHA256: C2ABDA30595DE61F77CA4DB13AC654BA4C4D5E94B3DCF3EC7E5B012016FD86DB.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/SourceHerglotzLocal-final.log.
Independent audit pending.

The literal dyadic electric volume response paired with an actual regular
magnetic point column, and the reverse actual regular electric point
column paired with the magnetic volume response, are continuous on the
plane. Genuine source support and positive plane gap give actual local
integrability. The checked scalar/field bounds and actual globally bounded
J/K point columns derive disk L1 constants proportional to 1/d for the
electric response and log((T+R)/d) for the magnetic response. The latter
requires d <= T+R.

Actual integrable source subtraction proves the same bounds for genuine
coherent flux differences, with the actual coordinate L1 source difference.
No field error, flux convergence, kernel bound or trace identity is assumed.
These are local disk statements. Integrated tails, whole-plane coherent
error and physical finite-stack Green identification remain further work.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `c2abda30595de61f77ca4db13ac654ba4c4d5e94b3dcf3ec7e5b012016fd86db`. Independent log `lean/logs/SourceHerglotzLocal-root-audit.log`, SHA256 `6d18760a38313393520f5a8af11322f1102dbe40a17a3a36faeb2502432dfcf9`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
