# Derived shrinking-gap coherent constant limits

Frozen source: lean/SourceHerglotzScaling.lean.
SHA256: 524535D9DF35093D72B131029C115E18CD0579566DE8A1CAC7860C6CECE80098.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all three reports standard-only. Log: lean/logs/SourceHerglotzScaling-final.log.
Independent audit pending.

The explicit actual whole-plane electric coherent constant at d=gamma*a,
multiplied by a squared, tends to zero as a decreases to zero. The actual
magnetic constant obeys the same limit. The logarithmic term is treated
by the actual identity log(M/(gamma*a))=log(M)-log(gamma)-log(a) and the
genuine continuity of a*log(a), deriving a squared log(1/a) decay rather
than assuming it. Gamma and M are required nonzero for these algebraic
identities; physical applications supply positive gamma and T+R.

These are the actual constants from SourceHerglotzWhole. Applying them to
actual source errors and incident amplitudes, and physical finite-stack
Green identification, remain subsequent constructions.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `524535d9df35093d72b131029c115e18cd0579566de8a1cac7860c6cece80098`. Independent log `lean/logs/SourceHerglotzScaling-root-audit.log`, SHA256 `65f8e32cec55c2162be55202312673409bda2a3b31a0bac6a43ef4b4e77cfc46`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
