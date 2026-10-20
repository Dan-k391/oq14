# LocalZeroPropagation — connected-domain topology from an explicit ball rule

Source: `lean/LocalZeroPropagation.lean`

SHA256: `4BBF716799B7F3927778F90A0F22A46802D41E21837B0F3ABE8723F6D57B0DCC`

Evidence: `lean/logs/local-zero-propagation-check.log`. Final compile
exited zero without warnings, created an importable object (202512 bytes),
and emitted four selected reports containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The domain is open and preconnected in any pseudometric space. The
function has an arbitrary codomain with zero; continuity is unnecessary.
The local propagation premise is completely explicit: for every center
c in the domain and every positive-radius ball contained in the domain,
if the function is zero on a neighborhood of c, then it is zero at every
point of that ball. This premise must be independently supplied by the
actual PDE argument.

The set of zero germs is open by the neighborhood-filter topology. To
prove relative closedness, take a point x in its closure and a ball of
radius delta around x contained in the domain. A zero-germ center within
delta/4 of x has its ball of radius delta/2 inside that domain. The
explicit local propagation premise makes the function zero on this ball,
which contains a neighborhood of x. Thus x itself is a zero germ.

Preconnectedness then makes the nonempty relatively open-and-closed
zero-germ set contain the entire domain. One zero germ or one positive
open ball of zeros consequently implies zero everywhere in the domain.
The local ball rule is never inferred from topology or continuity.

Self-review checked the overlap distances and strict radius margins,
domain containment of both ball and center, zero-neighborhood inference,
relative closure rather than global closedness, the nonempty germ
premise, and the exact preconnectedness theorem. No PDE, analyticity,
scalar Rellich, or local unique-continuation conclusion is assumed
implicitly.

Root independently read the complete final source at the recorded hash
and passed all four exports. Source frozen.
