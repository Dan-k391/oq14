# ModalScaling — actual spatial dilation at prescribed real frequency

Source: `lean/ModalScaling.lean`

SHA256: `644CF4D8E799937F4230F270A7259056A8E9EDE9F8EDB2542CF9201E270DB353`

Evidence: `lean/logs/modal-scaling-check.log`. All 24 selected exports
compiled cleanly with an importable object and only `propext`,
`Classical.choice`, and `Quot.sound`.

For a positive physical radius s, dilation is the actual coordinate
pullback F_s(x) = F(x/s). The derivative chain rule gives the coordinate
derivative and classical curl factor 1/s at points with the stated
differentiability. The global weak equation proof uses an actual change of
variables in Lebesgue measure, with Jacobian s cubed, and the pulled-back
compact C2 test function. The resulting weak curl pairing factor is s
squared. Thus the actual dilated Maxwell fields have frequency k/s and
coefficient n squared inside the radius-s sphere and one outside.

The radius-normal cross product is unchanged by positive dilation. The
exact exponentially weighted radiation defect equals s times the original
defect at x/s. This proves the outgoing condition along every path escaping
to infinity. Each actual ray far field is s times the original far field,
and the nonzero residue gives nonzero electric and magnetic far fields in
one common direction. Both dilated fields are therefore nonzero as actual
functions. The positive real dielectric bounds also survive dilation.

The final existence export chooses an actual high-quality dimensionless
residue pole k with positive real part and sets s = Re(k)/k0 for any k0 > 0.
The new frequency has real part k0, negative imaginary part, and exactly the
same quality quotient. The same residue input supplies the weak fields,
radiation condition, and the two actual nonzero ray limits.

Self-review checked the Jacobian and derivative factors, test support
transport, coefficient interface inequality including its boundary, normal
normalization at zero, complex-frequency exponential scaling, real versus
complex radius casts, far-field factor s, and quotient preservation. The
zero imaginary-part case in the standalone quotient identity is handled by
Lean's usual total division; the existence theorem has strictly negative
imaginary part.

Scope: the final theorem records the original dimensionless shell response
pole. It does not prove the meromorphic order of a separately defined
rescaled response or identify the full Maxwell resolvent. Cross-degree
separation, reciprocal residue normalization, and hotspot packing remain
separate tasks. Root independently read the complete final source at the
recorded hash and passed the audit of all 24 exports. The source is frozen.
