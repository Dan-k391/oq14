# RadialWeight verification

Frozen source: `lean/RadialWeight.lean`.
SHA256: `EBE210D4CB82405866474E037438ED20C667F830BFA0423397D833DDCD3CF47F`.

The weight is the actual function w(r)=2*r*beta(r^2), where beta is the proved
smooth nonnegative bump from RadialPowerTest. On the positive radial half-line
it is nonnegative and vanishes outside [1,2]. The globally defined function
also has a negative-radius part; global compact support in [-2,2] and
continuity prove honest global integrability, hence integrability on the
positive half-line.

The genuine positive-half-line change of variables r->r^2 identifies the
weight integral with the beta integral. Beta's proved vanishing outside
[1,3] identifies that with primitive(1), already proved strictly positive.
The total mass is therefore exact and strictly positive, rather than an
assumed normalization.

The actual Lebesgue radius scaling r=a*u, with a>0, proves the requested
weighted substitution for any real function F. This identity uses the general
measure-scaling theorem; it does not need to posit integrability or a flux
limit. The positive scaled density is defined exactly as
scaledWeight(a,r)=(2/a^2)*r*beta(r^2/a^2). It is nonnegative for r>0, vanishes
for 0<=r<=a, is integrable on the positive half-line, and has the same exact
strictly positive total mass primitive(1).

Pinned Lean 4.19 compilation and importable object export completed with exit 0 and no warnings. All 19 selected theorem dependency reports contain only propext, Classical.choice, and Quot.sound. Root independently read and accepted the full mathematical source chain.

Root gave final freeze approval at the recorded source hash.
