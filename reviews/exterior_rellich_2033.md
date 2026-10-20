# Exterior uniqueness integration checkpoint

The 1835-declaration clean aggregate at commit
`44ca66d9d6db10e555ae1881bdc1399aefb88100` passed. All 15 diagnostic groups
also passed at that clean commit. PDF packaging was withheld because two
lines overflowed; the next source includes the layout correction.

The 2033 batch adds 198 audited exports in 24 modules. Every new source
compiled individually with standard foundations only, and received a full
mathematical source review. The central root modules additionally received
independent 6.1 Sol recompilation and review. Shared configuration now
contains 176 modules and 148 libraries. The clean aggregate and PDF package
for this new batch remain pending.

Actual exterior uniqueness is derived from Maxwell and Helmholtz
equations, genuine Green identities, actual angular integrals, proved
harmonic density, and actual Hankel ODE uniqueness. Interior continuation,
global solvability and the complete channel/hotspot constructions are
not claimed by these results.

Targeted source hashes below precede Git newline normalization. The clean
aggregate provenance will record the exact packaged bytes.

- `FiniteRankAnalyticJets` (6): `8c084403517571a644d9624ebc5e80794e2e83c184227c5037a5fb7caa6f3f93`
- `CompactLaurent` (1): `550a1ea4f1736f0c44dd598a54cab294a83d33f1cc9b4f14cfecdd27cf5506fa`
- `VolumeLaurent` (1): `e634f447a62f63bb1fec01ab4782fcd8026778046281abe0ef1fbf624b2aba60`
- `ComplexVolumeReciprocity` (9): `0b7cb8583b7809a3c85365b0a774c8efc9cce3910190f500b790fc85b00eed1f`
- `RadialRellich` (20): `775a2375fd3e936c550b9a5da7bc22182d49d2a58e8681d93a168e5b74e29b04`
- `RadialMoment` (17): `ee99e87a6542c05bd07ad2886f5ea51cade334a43e7fff996fbb5c2896cd90d2`
- `RadialMomentODE` (4): `b800b8771d3acdafb78fd5f963a53012037056b541f28b55913dcb12c894b8de`
- `SpherePolynomial` (5): `e22b5ae5a7bab6a7837f68cacdb48918c5169b669c4c147cb86dba74a5632f02`
- `HarmonicPolynomial` (21): `4d6b0d247f70e0d46dd07d747ac5c1dbe5c1ae02787ee15996f5db27cbde80cc`
- `FischerDecomposition` (11): `4d37ceae3e494724c3b09bc2f99505501e6e25da4a7d93ea3cdce9a87c064108`
- `HelmholtzTestCalculus` (7): `b3fae1ebdfaac66c0548ebd3c993715adb266725493d438827dea8b269608c8d`
- `ExteriorGreen` (11): `01ff2b9a36e06c5b93ac6a308589d2396f36ede7e1003d690dc314a0c1ebccb7`
- `RadialNormTest` (8): `b87c76a323dc610591086fb962e1694aaab65fc088df5a27a15ae45c2d918027`
- `ComplexPolarIntegration` (8): `0dcac8c3e86cbca43cae89b466d5690ee5e17213b719ef27387b63b7b87449a1`
- `HarmonicMomentSeparation` (3): `77761814aa36d30ed41d856494211201978e3e323f8d225a3f400065be2ae525`
- `OneDimensionalGreen` (11): `6b37503ab59b24351fa22cb068847ba02c403a98a4078ddc6757c35b81c625f8`
- `RadialMomentRegularity` (4): `a5575d1fa08afb8a76f29eeccd5650e4973eb23433757d97c43c847441b947f9`
- `RadialMomentWeights` (9): `263f3ac62aba656ca75fd9c81f35abd499803a2b3c95a994fd724d6ebab8cd12`
- `RadialMomentClassical` (4): `3ca1d5aca8a0a112360d835eb2a6a89bd145f000b271cdbec1073cfc21aed53e`
- `SphericalMomentEquation` (9): `c23ea85e25bb4d6d185650f99fb179faa8e9110a10d717735d1f93e7623f68d2`
- `ScalarExteriorRellich` (3): `239708022d890544e618c3cace2bf6d9a3e90d1fd099a31a4d4af76009aba9a2`
- `ComponentAngularEnergy` (9): `b03bea48672524e6de56689a34d9ca369e7e569e5b1f46861d764685b5beae05`
- `MaxwellExteriorRellich` (5): `44ae2a32999b21289cdd2e8a4e24ea66b07a32d3d2e5ba9aa84cf95b9ac46a28`
- `SpatialKernelAnalytic` (12): `5001cdb257ad2e0f15e393c84ade2de81d1cf0ef30a9a8cb7ae236efff585f33`

Only surplus final blank lines were removed during integration from: reviews\maxwell_formalization.md. Theorem source content is unchanged.

Mixed-line-ending surplus final blank lines were also removed from: lean\HarmonicPolynomial.lean, lean\FischerDecomposition.lean, lean\RadialMomentRegularity.lean, lean\RadialMomentWeights.lean, lean\RadialMomentClassical.lean. No theorem statement or proof changed.
