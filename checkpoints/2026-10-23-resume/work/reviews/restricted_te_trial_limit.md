# Whole-plane dynamic-static limit for actual scaled harmonic TE fields

Frozen source: lean/RestrictedTETrialLimit.lean, SHA256 3C6D9DBB12D869A53C75B912ED272330E3C9E0802A70C999E727FB02ED901CCC.
Author final pinned compiler/object PASS: exit 0, no warnings, three standard-only reports. Log: lean/logs/RestrictedTETrialLimit-final.log. Independent audit pending.

Actual coefficient scaling gives the exact coherent-error scaling and the literal free-total-field flux identity. For a fixed actual finite harmonic TE input scaled by a inverse, actual source gap gamma*a and source mass at most M*a² imply whole-plane L1 convergence of the literal free total-field flux to its actual static coherent expression. The proof combines the derived gap-uniform harmonic coherent bound with the genuine quadratic outgoing source estimate; both error budgets tend to zero. Source admissibility and mass are physical source premises here, discharged for the constructed actual inverse by RestrictedTESourceMass. No plane convergence, magnetic identity or compact-point representation is assumed. The parity reaction remainder and physical finite-stack lift are separate from this free-flux theorem.
