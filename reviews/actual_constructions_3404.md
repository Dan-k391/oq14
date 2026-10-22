# Audited actual constructions: 3404

October 22, 2026. All 242 new reports have independent full-source and
pinned-compiler audits. A clean aggregate for this revision is pending.

## Actual static cone, complete scalar stack sum and finite sphere asymptotics

A further 242 declarations in 40 modules have complete-source and independent
pinned-compiler audits. Registered totals are 3404 reports, 323 modules and
295 libraries. The new aggregate revision needs its own clean combined build;
the completed clean 3162 release is preserved separately.

`RadialPhaseLimit`, `RadialParityLimit` and `RadialPairedFamily` derive the
actual outgoing coefficient limit along a common sequence of physical
finite radial stacks, for both polarizations and common material bounds.
`RiccatiFactorialTail`, `RadialMiddleTail`, `RadialLowTail` and
`RadialFullMajorant` combine the actual low, intermediate and high degree
estimates into a fixed summable majorant. `RadialScalarSeries`,
`RadialScalarUniform`, `RadialPairedScalar` and
`RadialScalarDifferentiation` prove convergence of the entire scalar sum
and its actual mixed derivatives, uniformly on compact complex disk
products and with each fixed degree weight. These are actual derivatives
of the sum, rather than merely convergent formal differentiated series.
The spatial dyadic Maxwell reconstruction remains a separate requirement.

The conical radial, angular and spatial test modules prove the actual weak
gradient, zero weak curl and zero weighted divergence of the literal
singular static field. `ConicalStaticField` assembles existence from the
actual shooting root, with exponent in (0,1), finite local energy, common
positive permittivity bounds and uniform blowup on an open cone of positive
measure. The singular field is static. Preserving its nonzero coefficient
under a positive-frequency Maxwell correction remains unfinished.

The static sphere residual, forcing, scale and small-error modules derive
the actual inverse error from incident variation. The finite sphere modules
extend this to multiple separated balls, including moving centers, with
actual cross-Newton interactions and derived perturbation smallness.
`FiniteSphereAsymptotics` proves the actual weighted and physical L2 errors
of order a*sqrt(a), and coordinate L1 error of order a^3, under explicit
incident derivative and center-amplitude bounds of order 1/a. It uses the
actual parity limiting kernel; its identification with finite physical
stacks remains a separate step. `StaticBallDipole` proves the actual source
moment and exact exterior Newton point-dipole identity.

`DebyeCalculus` and `DebyeMaxwell` derive genuine local vector Maxwell
equations for both Debye polarizations from an actual smooth scalar
Helmholtz solution. `LocalRadialHarmonic` derives the spatial scalar equation
from an actual radial ODE and a homogeneous harmonic polynomial.
`EntireFactorialSeries` proves actual differentiation of factorially bounded
entire series. These bridges do not by themselves supply the normalized
spherical basis, its addition identities or full spatial Green series.

Final sources and independent logs:

- `RadialPhaseLimit` (16): `0355ef8aac36fdd1545c1b6eb375fa0134f332502a5d1fd9f2ae379ca215a913`; `lean/logs/RadialPhaseLimit-independent-continuation.log`.
- `RadialParityLimit` (8): `35db70b972b82142170f6a26e1b6376412225b54f1740d37070e841b6258c8cf`; `lean/logs/RadialParityLimit-independent-continuation.log`.
- `RadialPairedFamily` (16): `66d2dd297f1993a612024bab47434c8af77478b11568361bed8a7dc885a4caac`; `lean/logs/RadialPairedFamily-independent-continuation.log`.
- `RiccatiFactorialTail` (7): `8f0e7b666a7272972fd79fcdf9e8ea8c8a754646cc40b56fbe6234bf5a45103d`; `lean/logs/RiccatiFactorialTail-root-audit.log`.
- `RadialMiddleTail` (11): `7b1248c3709f273cbd6cf49a194f360b8f2bcb9696b3e126c40ce185f69c0464`; `lean/logs/RadialMiddleTail-root-audit.log`.
- `RadialLowTail` (8): `c2c0cba4ee0eb93a751e6b342658bf33a1debbe872dc40aa57a7bbae4a548b84`; `lean/logs/RadialLowTail-root-audit.log`.
- `RadialFullMajorant` (5): `82d10091f2d26c478203868b4e965238daeed95f2ea70ee9a93fcbf24a5c9293`; `lean/logs/RadialFullMajorant-root-audit.log`.
- `RadialScalarSeries` (6): `50a096e821e93308f8e84161cf5d3d9cc55cc3e90d1782965a3a0a2a68a4b7d9`; `lean/logs/RadialScalarSeries-root-audit.log`.
- `RadialScalarUniform` (10): `2cc30dc3b17664ac4ee92eae9c9df96954c67245d7797bf7ffa82ea319071f14`; `lean/logs/RadialScalarUniform-root-audit.log`.
- `RadialPairedScalar` (8): `72300532aa4860f938804649481505f590653d41aa8ace3fd0c643a67943e86f`; `lean/logs/RadialPairedScalar-root-audit.log`.
- `RadialScalarDifferentiation` (9): `ed7caf36bf4033656aeb8074c0239c619bbcce962d005269967a9aa5a47567a3`; `lean/logs/RadialScalarDifferentiation-root-audit.log`.
- `ConicalRadialTests` (4): `8d32233882b39bd3b5caba3a23f90aa54a3dd0e2bebf7fea9e0e0200d7a69bff`; `lean/logs/ConicalRadialTests-root-audit.log`.
- `ConicalNontrivial` (9): `e420640a809e9e4478d2b3a0bc0f479755bdf8f634aab7f78e347db38499ab3f`; `lean/logs/ConicalNontrivial-root-audit.log`.
- `ConicalPolarTests` (3): `b5a8b30edad67c59b624f696df18b41c88f9caed3235dae5a56108d55f82b077`; `lean/logs/ConicalPolarTests-root-audit.log`.
- `ConicalAngularTests` (4): `b06c4b2d6ad676693410c9afa9b65b60c1b86b32c30a5bcc219ebb9b6b4745a8`; `lean/logs/ConicalAngularTests-root-audit.log`.
- `ConicalSpatialTests` (7): `6e919bc8ed81f2bf991698572efdc7c2cda09e9cf441eb21f0fef01a5c70e60a`; `lean/logs/ConicalSpatialTests-root-audit.log`.
- `ConicalSpatialWeak` (4): `3f55ccd035eb53b35ae76f46b1900d38e87c1d48f17ff973bc4804f7c7d53c0c`; `lean/logs/ConicalSpatialWeak-root-audit.log`.
- `ConicalWeakGradient` (2): `862a55b5ad1e8e56d2cb4d37fbe99355ea365db3247ca0c7002914c48cc1af49`; `lean/logs/ConicalWeakGradient-root-audit.log`.
- `ConicalDivergenceTests` (2): `84ede3958b46a019cc4e469aa1a0b3edd160c6a88122961754228f460091f6bc`; `lean/logs/ConicalDivergenceTests-root-audit.log`.
- `ConicalStaticDivergence` (4): `b2ec3773691349f15018d35a2c81ba79c103d5e68aa82e717807241beb82933e`; `lean/logs/ConicalStaticDivergence-root-audit.log`.
- `ConicalWeakCurl` (3): `ae62560514e08609bf887abd70a44ffb7e7bf44c7c4e042c6a148ff40c8aba4f`; `lean/logs/ConicalWeakCurl-root-audit.log`.
- `ConicalStaticField` (3): `8e8171706dec049f46f3328e97c6fe205dec7e13f78cdbbb565219a2ef3d712a`; `lean/logs/ConicalStaticField-root-audit.log`.
- `StaticSphereResidual` (6): `ecdcbb2ee94a379451e53ef3dcee6affc0fbcda3810e0ed3fae63993ee7a2323`; `lean/logs/StaticSphereResidual-root-audit.log`.
- `StaticSphereForcing` (4): `abae829b7e55e5cc40b131116162e62ad2f879cebbbb1fe3e225239b1dce9f79`; `lean/logs/StaticSphereForcing-root-audit.log`.
- `StaticBallInteraction` (5): `c5dff3e5163c1050e1c467a2dcf8c6cda509a8c1a945bd5c18c2c86e46d1aa5d`; `lean/logs/StaticBallInteraction-root-audit.log`.
- `StaticSphereScale` (9): `80c7a03793772fd8dbd127c2be9d697a50de4951447303776815ef88387582f9`; `lean/logs/StaticSphereScale-root-audit.log`.
- `StaticSphereSmallError` (2): `91b5eb31ce949a12109f7f6de7cb244237caa885cbb1ae757495cc28e40a2288`; `lean/logs/StaticSphereSmallError-root-audit.log`.
- `StaticSphereAsymptotics` (2): `a5341c77541ae25a22d98827166aeee4395c29f1bbe4cb96bcca9139e9784ff8`; `lean/logs/StaticSphereAsymptotics-root-audit.log`.
- `FiniteSphereStatic` (9): `a7ec45804b75ad671044e460bbc057f4a0602f7adc7a76c4363bdb7e5fece04e`; `lean/logs/FiniteSphereStatic-root-audit.log`.
- `FiniteSphereResidual` (2): `d0bed195731da120f4f037ffa174b690a8c02622f76e3c865c6e8b0e80247a5a`; `lean/logs/FiniteSphereResidual-root-audit.log`.
- `FiniteSphereResidualBound` (3): `850a7982c950bc301a57a8d33b44ab9e50dfc56c11da1b5eba710806c9a13d62`; `lean/logs/FiniteSphereResidualBound-root-audit.log`.
- `FiniteSphereComparison` (3): `dfb4f047f20073281d96d53a3cdfc994eaf15937f6a81092835b56476a2db642`; `lean/logs/FiniteSphereComparison-root-audit.log`.
- `FiniteSphereScale` (6): `c017c84f477cf6cd845f041c00389b515300dccd1ddf8d703a77d1ce059cc5d2`; `lean/logs/FiniteSphereScale-root-audit.log`.
- `FiniteSphereSmallError` (3): `da69eadcb1af5db2caa39e0a5a732944e75c0e20631b20c969388c4d54b76187`; `lean/logs/FiniteSphereSmallError-root-audit.log`.
- `FiniteSphereAsymptotics` (1): `9da4d2b4215c9525794ab05baa0ad7afea55e6beff264117a24ad98c2f03366f`; `lean/logs/FiniteSphereAsymptotics-root-audit.log`.
- `StaticBallDipole` (6): `fc42e2e1ab48cc0ef5401b08469163e2f805ff0257aaa0ffc60091ae083a748a`; `lean/logs/StaticBallDipole-root-audit.log`.
- `DebyeCalculus` (15): `3f5fa7d236832bd4a1f1f4256fd8b6411b386bd380d0dd1d1c436ff9b78fe5a9`; `lean/logs/DebyeCalculus-independent-continuation.log`.
- `DebyeMaxwell` (4): `5bf62031a047fb57ad9696d9dda79e975aa0f2abb8bdf43be2e826344e0c4486`; `lean/logs/DebyeMaxwell-independent-continuation.log`.
- `LocalRadialHarmonic` (6): `cd2429a35cd58b9241492ece3349b609085f4b9f554c4bde36e37391ba1c1be3`; `lean/logs/LocalRadialHarmonic-independent-continuation.log`.
- `EntireFactorialSeries` (7): `955005376d77270cbd520e0c86205cd317169053c12b74d5d7d247a5f8ace4fa`; `lean/logs/EntireFactorialSeries-root-audit.log`.
