# Weak Maxwell equations from actual bounded derivatives

Frozen source: lean/BoundedMaxwellWeak.lean.
SHA256: 5EEC677D54AB09F9BB66887D8CF97A8CD02372CD5FF94E43929501675226D0BC.
Final pinned compiler/object PASS: exit 0, no warnings, one report using
standard foundations only. Log: lean/logs/BoundedMaxwellWeak-final.log.
Independent audit pending.

Actual globally differentiable Maxwell fields with uniformly bounded first
Frechet derivatives satisfy the real compact-test Maxwell equations. The
partial derivatives are measurable and their actual bounds give local
integrability. Existing RadialInterface integration by parts yields the weak
law, with no C1 premise and no assumed weak equation. The generic pointwise
Maxwell law is discharged for literal finite parity illumination separately.
