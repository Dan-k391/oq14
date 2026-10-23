# Genuine quadratic source-source Maxwell flux with explicit gap control

Frozen source: lean/PlaneQuadraticFlux.lean.
SHA256: 3D3502DDEA1D99DEADC53298E150A7DF0D9C4BD7EF66D4946B48710195FE27AF.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all six reports standard-only. Log: lean/logs/PlaneQuadraticFlux-final.log.
Root independent complete-source mathematical audit and pinned compiler PASS: exit 0, no warnings, standard-only foundations.

The actual magnetic volume field has an everywhere-on-plane bound
2*abs(k)/(4*pi)*(abs(k)/d+1/d^2)*sourceMass, derived from the actual gradient
kernel and genuine plane/source gap. Combining this with the actual electric
disk L1 estimate gives a quadratic normal-flux disk constant of order
1/d^3+1/d^2. Actual transverse leading cancellation supplies the integrated
inverse-cube radiation tail independently of the gap. The whole-plane bound
and its actual source-subtraction difference bound are proved for arbitrary
separated compact genuine sources. No pointwise magnetic bound, field
identity, whole-plane bound or tail conclusion is supplied as an assumption.

The explicit wholeConstant retains frequency, enclosing radius, disk radius
and gap dependence. Source smallness and moving-gap convergence are subsequent
specializations. These are literal outgoing volume fields; physical finite-
stack Green reconstruction remains separate.
