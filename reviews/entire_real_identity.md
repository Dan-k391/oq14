# Actual real-interval identity bridge

Frozen source: lean/EntireRealIdentity.lean.
SHA256: 2F7FCC25169B4639462D35C12465071609BE9683F5C3A4EB61E9D562134F57BD.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/EntireRealIdentity-final.log.
Independent audit pending.

An actual entire function vanishing on a nonempty real interval vanishes
everywhere. The proof constructs an explicit nonzero real sequence of zeros
converging to zero and applies the actual complex analytic identity theorem.
Consequently a literal finite sum of quadratic exponential packets with
distinct frequencies, vanishing on that real interval, has every coefficient
zero. No continuation or independence statement is supplied as a premise.
This is an intermediate bridge toward the actual two-dimensional symmetric
scalar-jet surjectivity; finite-power and finite-band realization are separate.
