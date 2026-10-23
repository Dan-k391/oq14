# Actual Hermitian Gram completion

Frozen source: lean/HermitianGramCompletion.lean.
Author final pinned compiler/object PASS: exit 0, no warnings, two standard-only reports. Log: lean/logs/HermitianGramCompletion-final.log. Exact source hash below; Root independent complete-source mathematical review and fresh pinned compiler PASS, no warnings and standard-only foundations.

For every actual finite Hermitian complex matrix G, the spectral theorem constructs an explicit positive real scale 1+sum of absolute eigenvalues. The actual matrix scale I-G is positive semidefinite, derived by conjugating the nonnegative diagonal eigenvalue gap. The proved positive square-root factorization then constructs B with B-Hermitian-transpose times B=scale I-G. No matrix positivity, norm bound, completion factor, or Gram conclusion is assumed. The pinned Matrix.PosDef dependency was built locally without changing configuration; dependency log HermitianGramCompletion-dependency.log.
SHA256: 33AAB6BD03E287423E3CCA1FE5719F7BF2DAF1B87EFEDA945EAD99D775BB4CA8.
