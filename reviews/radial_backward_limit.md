# Independent audit of actual inward finite-stack limits

Source: `lean/RadialBackwardLimit.lean`.
SHA256: `19CFD7ADC3835C290018CAD379F57EA57DF0ACEF6B361BB3A886211320604DC5`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Exit 0, no warnings, and all ten reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/RadialBackwardLimit-independent-continuation.log`.

The actual reverse transfer is proved equal to the inverse forward transfer
by the literal fundamental matrices. Forward actual columns therefore give
the actual reverse state, with its determinant-one inverse formula. The
proved forward single-layer limits and convergence of the input state imply
the actual backward layer limit. The reference inverse is identified with
the actual constant ODE solution at negative width.

The inward finite-list state recursively traverses outer segments before
inner segments. Its limit is derived inductively; no propagated limit is
assumed. The actual finite layers are in the same outer-to-inner order,
and the recursively derived retreat is identified with the existing actual
RadialStack.traverse on those layers.

Scope: fixed angular degree and fixed finite segment list, fixed positive
coefficients and widths, and common radius tending to infinity. No uniform
limit for increasing degree or layer count, or spatial Maxwell Green limit,
is claimed.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 10 reports using only standard foundations. Final source SHA256 `19cfd7adc3835c290018cad379f57ea57df0acef6b361bb3a886211320604dc5`. Independent log: `lean/logs/RadialBackwardLimit-independent-continuation.log`; log SHA256 `fcc367cdcad9489d8c107fed14b564bfb8390a263bbfd1c35be986d38067e08b`. This certifies the stated scope, not either complete OQ14 construction.
