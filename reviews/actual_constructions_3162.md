# Audited actual constructions: 3162

October 22, 2026. All 358 new reports have independent full-source and
pinned-compiler audits. Registered: 3162 reports, 283 modules, 255 libraries.
A clean aggregate for this revision is pending.

## Actual sphere H1, scalar stack limits and spherical inclusion response

A further 358 declarations in 36 modules have complete-source and independent
pinned-compiler audits. The new aggregate revision still needs its own clean
combined build. The completed clean 2804 release is preserved separately.

`CapSturmEndpointTest`, `CapProfileFirstOrder`, `SphereAxialTests`,
`SphereCapWeak`, `SphereAxialSurface`, `SphereSurfaceTests` and
`SphereSurfaceFubini` derive the actual spherical weak identities for
arbitrary ambient C1 tests, including integrable pole behavior, periodic
azimuth cancellation and the curvature term in all three tangential
gradient components. `SphereCapH1` proves L2 membership, actual weak
tangential differentiation, a nonzero L2 class, positive mass and a normalized
H1 eigenfunction from the actual shooting root, with exponent in (0,1).
Its H1 definition explicitly states these distribution identities; no
equivalence with an abstract manifold Sobolev library is claimed.
`ConicalCapField` constructs literal spatial potential and electric
candidate, proves global Borel representatives, local L2 membership,
continuity of the potential at the origin and a nonzero angular electric
factor. Its spatial weak-gradient and transmission equations, and the
finite-frequency Maxwell correction, are still subsequent work.

`RiccatiBarrierNormalization` and `RiccatiGaussianBound` prove the actual
Gaussian regular lower bound. `RadialHighOrderBound`, `RadialHighOrderTail`
and `RadialStackHighTail` derive actual high-degree reaction estimates,
absolute weighted summability and decay faster than every fixed inverse
power of the radius for common bounded-index chains.
`RadialReactionKernel` and `RadialReactionTail` identify the literal scalar
Green reaction and its first mixed derivatives. `RiccatiCompactDerivatives`,
`RadialEntireReaction` and `RadialEntireTail` extend these scalar results to
every fixed derivative order on compact complex disks, including the
analytic origin. Constants and larger comparison disks are independent of
degree and radius. `RadialIntermediateBound` supplies an actual exponential
bound in the complementary degree window. Summing that window and the full
spatial dyadic reconstruction remain separate requirements.

`RadialGluing` proves literal radial matching. `RadialReference` constructs
the exact constant-coefficient sine/cosine transfer and quarter-wave powers.
`RadialApproximation` derives the actual radial/reference error of order
R^-2 for fixed layer width and degree. `RadialFiniteLimit` constructs
physical shared-radius lists and proves their forward finite-stack limit.
`RadialBackwardLimit` proves inverse transfer identities, the backward
finite-stack limit and equality with the existing actual traversal.
These are fixed-degree, fixed-finite-stack results. The outgoing coefficient
parity limit and spatial Green identification are not supplied as premises
or inferred from those results alone.

`StaticBallPotential`, `StaticBallHessian`, `StaticBallL2`,
`StaticBallSchwartz`, `StaticBallFourier`, `StaticBallSymbol` and
`StaticBallNewton` derive the genuine uniform-ball potential, weak Hessian,
Schwartz identities, Fourier symbol and its identification with the existing
Newton operator. The interior action is actually -P/3.
`StaticSpherePolarization` proves the exact isolated-sphere response.
`StaticBallTranslation` and `StaticBallCentered` establish it at any center
through actual measure-preserving translation and translated weak pairings.
`StaticSphereMaterial` proves the exact weighted block and inverse action;
the weighted trial is 3 sqrt(chi)/(chi+3) E and its physical polarization is
3 chi/(chi+3) E, including chi=0. Quantitative varying-field, multiple-ball,
finite-frequency and shrinking-gap source estimates remain subsequent work.

Final sources and independent logs:

- `CapSturmEndpointTest` (2): `51908019f5f8faddd3f41f0b9ca3e6e089024159be606851342d9b08cd70a7fe`; `lean/logs/CapSturmEndpointTest-root-audit.log`.
- `RadialGluing` (18): `f1910754f80ff90199402a64dd184ffe3e78e5fc069db461a0cf688de97cc272`; `lean/logs/RadialGluing-independent-continuation.log`.
- `RiccatiBarrierNormalization` (14): `34a109fe63b1fa1c0b1cfc3d591a264df39464e8ec580d3e1eb038fa1da45753`; `lean/logs/RiccatiBarrierNormalization-root-audit.log`.
- `RiccatiGaussianBound` (15): `42322ee69836fad2fa012b816630ed047082ca029319a45376e677cda2826be4`; `lean/logs/RiccatiGaussianBound-root-audit.log`.
- `SphereAxialTests` (15): `94382d92104e50d593804ba31b46eb3ae95739d82dcaca12d95b9fbaebd0d2cd`; `lean/logs/SphereAxialTests-root-audit.log`.
- `StaticBallPotential` (14): `47ccc48bf55da2bf9dafabb918d749f1b6cc5ff7f902a95c590948e66b1d507c`; `lean/logs/StaticBallPotential-root-audit.log`.
- `StaticBallHessian` (14): `6cfa65cfdf9de09786c581937e271e1b65d57a67ba32de7e5b27c1f8f0de7693`; `lean/logs/StaticBallHessian-root-audit.log`.
- `SphereCapWeak` (12): `beec95f73fa3c463df61eed9f690fc18eb9687cd1ddbd3d98b9191445353a8cd`; `lean/logs/SphereCapWeak-root-audit-20261022.log`.
- `CapProfileFirstOrder` (4): `32df59a9cf8b9d4cce77db2865557b30478f53d0093812b97bd31ed73d48b6a2`; `lean/logs/CapProfileFirstOrder-root-audit.log`.
- `RadialHighOrderBound` (9): `468b35c302a2c3c44112e949b6fb423058d62441586bcb5a0593562411949da7`; `lean/logs/RadialHighOrderBound-root-audit.log`.
- `RadialHighOrderTail` (12): `ccd63c15a63e82979d576fa8707e58c55fccebb94cfe4cc43e6684d50d908dcb`; `lean/logs/RadialHighOrderTail-root-audit.log`.
- `RadialStackHighTail` (9): `1bace4b17b0d2c4a8e59210f478a1cd87609fd9433235c9c79145ca701f409a2`; `lean/logs/RadialStackHighTail-root-audit.log`.
- `SphereAxialSurface` (7): `714763ddd4b2917618f781d5e18267bcacef5d5cd5d9995188670aae23f17d13`; `lean/logs/SphereAxialSurface-root-audit.log`.
- `StaticBallL2` (11): `7b7046d2c6993a864df0636fc5c389675ddbb58c9ec8976bfdeabb45bbc2d1ae`; `lean/logs/StaticBallL2-root-audit.log`.
- `RadialReference` (7): `f0b34f787f3d3941dfed3c5f34e3487d000215087bf63433ed00fa769a6dbc11`; `lean/logs/RadialReference-independent-continuation.log`.
- `StaticBallSchwartz` (7): `c5f2d5d6d25eb79a00f99f239d612f95065e7125d0e77447bd4e1fb621b653ab`; `lean/logs/StaticBallSchwartz-root-audit.log`.
- `StaticBallFourier` (3): `54b4e0efb67ba888e5204c81a4dd6fcda6b3af471ea9e63c6ddd7f442301d620`; `lean/logs/StaticBallFourier-root-audit.log`.
- `RadialReactionKernel` (10): `81f3164698e7db64d66b4ce0b43cbad1cb32f52ee3bb97c1d81d6753cc9773b5`; `lean/logs/RadialReactionKernel-root-audit.log`.
- `RadialReactionTail` (6): `8e9123219889cac708179748e0cc567e7d90b0895f014cf1e885957ab37ef8c3`; `lean/logs/RadialReactionTail-root-audit.log`.
- `SphereSurfaceTests` (22): `b2e7d664074ff652cd778ee0375b468deb22f891cedc867de270d8d20073d7e5`; `lean/logs/SphereSurfaceTests-root-audit.log`.
- `SphereSurfaceFubini` (6): `628b319febe2b7b2856276b6b54183ea32f3b786593ea0d50392c7958936c997`; `lean/logs/SphereSurfaceFubini-root-audit.log`.
- `StaticBallSymbol` (8): `61acc6a578026f8192c0eb679f152356f1b80658210e928d6d1ca53932520cb1`; `lean/logs/StaticBallSymbol-root-audit.log`.
- `RadialApproximation` (16): `f34f39613002663db40fccec32dd3bd035bc64a0554d636e9a219781053c347d`; `lean/logs/RadialApproximation-independent-continuation.log`.
- `SphereCapH1` (16): `d02daa57873973b2f67e529c11eb732418e893016b1b48e2aa75882f2b0111d2`; `lean/logs/SphereCapH1-root-audit-final.log`.
- `RiccatiCompactDerivatives` (9): `7fcbb27314530cf8d8e0cfa853f69c5551ca196972c70eed167c62179de6832a`; `lean/logs/RiccatiCompactDerivatives-root-audit-final.log`.
- `StaticBallNewton` (8): `5255f946da4b3732c9b0eb742836738239f0c877ebca619ec452cce53246ca12`; `lean/logs/StaticBallNewton-root-audit-final.log`.
- `StaticSpherePolarization` (4): `4d1c63f886d799d7927b31d92a7fea25097fcd7e1921d00398cd08cbfb4d1456`; `lean/logs/StaticSpherePolarization-root-audit-final.log`.
- `RadialEntireReaction` (7): `080e0b6f979b03cb3e920b5567a361e864d3bdffbab0b74c7e3d99b7801411cc`; `lean/logs/RadialEntireReaction-root-audit-final.log`.
- `RadialEntireTail` (7): `b2dbd5df9bf27c16cff0c26423aa0cb7d67e45beb3ada69b174d3e291680c046`; `lean/logs/RadialEntireTail-root-audit-final.log`.
- `RadialFiniteLimit` (10): `c9d404b3c08ffcde8ae16185fdc638e59d18339c0ab2a9f1ce5348afe90f76f4`; `lean/logs/RadialFiniteLimit-independent-continuation.log`.
- `StaticBallTranslation` (8): `d1c10524321a21fc650a257e62a834ac2a1bcef0448e18692ff8d649767f7f50`; `lean/logs/StaticBallTranslation-root-audit-final.log`.
- `StaticBallCentered` (6): `2353f4a9038fb44afb8654d98024c66add3087197cb805f02dfed35646352034`; `lean/logs/StaticBallCentered-root-audit-final.log`.
- `ConicalCapField` (21): `a54516fc04b820e15ea088f076333ae84bb199339946a79c90a2dac9be140246`; `lean/logs/ConicalCapField-root-audit-final.log`.
- `RadialIntermediateBound` (3): `6a474cff9aeb0fb2038c762d5b76b7080b461e53f4ef88c78b69b69c4c16e181`; `lean/logs/RadialIntermediateBound-root-audit-final.log`.
- `StaticSphereMaterial` (8): `34d6d749507d0ac2e2c0d92109e0591a72b3078f9f97a32112314857e7e2f001`; `lean/logs/StaticSphereMaterial-root-audit-final.log`.
- `RadialBackwardLimit` (10): `19cfd7adc3835c290018cad379f57ea57df0acef6b361bb3a886211320604dc5`; `lean/logs/RadialBackwardLimit-independent-continuation.log`.
