# Actual material fields, regional graphs and physical power

SmallVolumeMaxwell has six checked exports. The local incident field is
turned into its actual weighted datum, the proved inverse constructs the
volume unknown, and the actual electric and magnetic spatial responses are
locally L2. Both compact smooth test Maxwell equations are consequences.
The sufficient hypothesis is explicitly
`252 * c.bound * k^2 * R^2 < 1`. No general-size scattering assertion follows.
The classical-incident corollary derives the incoming test equations from
actual classical Maxwell equations.

MaterialHCurl has eight checked exports. The actual spatial curls are
`ikH` and `-ik epsilon E`. Their regional L2 membership is established,
and RegionalCurlUpgrade derives the compact C1 weak-curl definition from
the actual smooth-test equations. The constructed graph representatives
agree almost everywhere with the spatial fields, and satisfy both coupled
Maxwell equations. The small-volume result uses one inverse unknown on
every bounded open observation region, including interface-crossing regions.
No global L2 assumption, boundary condition, or material field equation
is introduced as an additional hypothesis.

MaterialPower has four checked exports. The existing graph-space local
power theorem is transferred to the actual spatial fields through proved
representative equality. A compact real C1 test fits inside an open ball;
its gradient vanishes outside its support, so restricted integrability
and conservation extend to ordinary volume integrability and the global
zero power pairing. The small-volume corollary constructs its unknown
from the inverse and then derives conservation.

Root targeted compilations succeeded and emitted importable objects for
all eighteen exports, with only propext, Classical.choice and Quot.sound.
Counterexamples independently read and approved SmallVolumeMaxwell6 and
MaterialHCurl8. Channels independently read and approved MaterialPower4,
including the representative substitution and global support argument.
These modules are a subsequent research batch, outside the saved
1058-declaration commit and its isolated aggregate build.
