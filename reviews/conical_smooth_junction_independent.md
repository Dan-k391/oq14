# ConicalSmoothJunction — independent root audit

PASS. Fresh pinned Lean 4.19.0 source check, exit 0, 12 qualified standard-only axiom reports, no compiler warnings or errors. Uses existing dependency objects; not a clean aggregate build.

Log: `lean/logs/ConicalSmoothJunction-root-audit.log`.
Source SHA256: `f618021d115ad76cdd2f66523f9bd0408de098d2cb139825169bc53186a809c2`.
Log SHA256: `79c039cb1a34e52bbca2eb88bfd3e10d407c3def375d36c37f0c41e3874a2ec2`.

Full source read. The expNegInvGlue derivative and smoothTransition quotient yield nonnegative transition derivative. The explicit inward corner has strictly positive partial derivatives in its two positive margins. The actual cone-ball region is open and bounded, with exact equality away from apex/corner neighborhoods and eventual agreement off the exceptional sets. Its defining function is smooth wherever the vertical coordinate is nonzero. Physical gradient nonvanishing, a global smooth-boundary conclusion and identification with the actual 3D material are not yet asserted.
