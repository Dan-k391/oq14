# Independent actual radial propagation audit

Source: `lean/RadialPropagation.lean`.
SHA256: `82C485D52574D5F1531C0266384CE44220A6941986971465A10527A4D0791124`.

Independent reviewer continuation_review_sol read the complete frozen source,
the actual layer construction and the reused barrier derivative proofs.
Independent pinned Lean 4.19 compilation exited 0 without warnings; all ten
reports are standard-only. Log:
`lean/logs/RadialPropagation-independent-continuation.log`. Source hash
unchanged after compilation; forbidden scan clean. No source edits.

The two-sided energy estimate follows from actual integrating-factor
monotonicity and the genuine derivative of |u|^2+|p|^2. The layer wrapper
discharges the ODE and derivative assumptions using actual Hankel solutions.
The generator bound is derived from positive inner radius, positive sigma,
and the actual l(l+1)/(sigma*x^2)-q^2/sigma potential. The barrier condition
q^2*b^2<=l(l+1) gives nonnegative potential throughout the interval, and an
actual nonpositive endpoint load forces the proved load/state monotonicity.
The endpoint-load hypothesis is explicit here and is discharged for outgoing
stack data in RadialStack.

Scope: actual homogeneous-layer ODE propagation and barrier estimates.
No full spatial Maxwell or all-order Green identification is asserted.
Mathematical and compiler audit: PASS.
