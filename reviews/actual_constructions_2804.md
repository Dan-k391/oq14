# Audited actual-construction integration: 2804

All 209 new declarations passed full-source and independent compiler audits.
There are 2804 reports, 247 modules and 219 libraries. This new revision has
targeted verification pending its own clean aggregate.

The clean 2390 milestone passed its aggregate, 15 diagnostics, 110-page PDF
and visual inspection. Local tag: oq14-maxwell-foundations-2390. Matching
artifacts: output/checkpoints/oq14-maxwell-foundations-2390/. Delivery SHA256:
011b8e9ed5767c25d8ae5ecf1f14b8a25731fa7910a794dfdc74ff0320cacf4e.

## Constructed radial sources, angular measure and material response

A further 209 declarations in 18 modules are independently audited.
`AxialCoordinates` (13) proves the actual Jacobian, injectivity and volume
change of variables outside a null plane. `SphereAxialMeasure` (20)
derives the sphere surface measure by cones, the latitude/azimuth integral
formula and zero measure of every latitude. Arbitrary-test angular weak
lifting and its H1 interpretation remain subsequent work.

`RiccatiRaising` (9), `RiccatiSeriesCoefficients` (11),
`RiccatiOriginSeries` (16), and `RiccatiOriginLimits` (14) derive the
entire regular series, its identification with the actual Hankel-defined
solution off zero, and both normalized origin limits. The entire series
is the extension at zero; the Laurent definition is not substituted there.
`RiccatiBarrier` (9) proves positivity of the regular solution and its
derivative. `RiccatiLogDerivative` (9) proves both logarithmic-derivative
bounds by a weighted Wronskian. The sharper Gaussian lower bound and
all-order summation remain separate.

`RadialLayer` (7) constructs homogeneous bases, actual solutions and
endpoint transfers. `RadialPropagation` (10) proves energy and barrier
estimates from those ODEs. `RadialStack` (17) derives estimates for exact
shared-radius chains, common material bounds and conserved imaginary
load. `RadialSource` (16) constructs outgoing core coefficients, a nonzero
denominator, negative imaginary reaction, low-order bound, core ODE,
normalized boundary matching and scalar Green branch-derivative jump.
`RadialLoadBounds` (8) derives the barrier reaction bound and both
normalized core source bounds. Full spatial Maxwell Green reconstruction
and all-order convergence are not already formalized by these results.

`SphereReactionKernel` (12) defines the literal sphere-integral parity
reaction and derives its bounds. `BoundedMaterialKernel` (17) constructs
the weighted L2 integral operator with its material-volume bound.
`ParityReactionVolume` (7) and `SmallParityInclusions` (5) derive uniform
invertibility for gain b/a and small finite balls. `ParityMaterialField`
(9) derives the unique inverse solution, norm estimates and actual
material relation for this explicit kernel. Identification with the
finite physical stack, exact static sphere polarization and the final
shrinking-gap whole-plane estimates remain separate.

Final source hashes before Git normalization:

- `AxialCoordinates` (13): `4e03176585805c595aa06a19745ced5fdc0246e69c62d4161d39523114c81147`
- `SphereAxialMeasure` (20): `bdc4611138aedfbf0a93f91861f22d53bbf2f0bc1f478f62330471c7e58f07c6`
- `SphereReactionKernel` (12): `084f2baa0bf822258bd6c5658be3624f981a697309fa29e766aed04157a6b5ce`
- `BoundedMaterialKernel` (17): `308e7338056f475f8271320043f3b3f1914227697bedaf46419773861e695e8e`
- `ParityReactionVolume` (7): `d2e5b6a0ca5da773ad96db8058490383f5292a72caee3919c5f20a3ee292f244`
- `SmallParityInclusions` (5): `3f0ff8a42f14403ceb7e91303ee070dbfe0ede0b91a4a917d5249ce132978097`
- `ParityMaterialField` (9): `de4fa6ee619b083be5cd862d89892e0a687ba4652290613523af59fbedf09c1f`
- `RiccatiRaising` (9): `14b756c4d53ffa224ee2264f03db32dc421fd6a691f9e37f69afbe151a8f9af6`
- `RiccatiSeriesCoefficients` (11): `85b49508569bcfb20e15bc24df28e36176a1b3eae9b0b754c2eb3da3d9aa6963`
- `RiccatiOriginSeries` (16): `dcdcde72d23543f682e07a47390d0687277548ed84f3d5da10caf8911de9392d`
- `RiccatiOriginLimits` (14): `0b8c8a722180d1fc813c02fd373e719e9d180692ccd9643a10a8f84f2c6277cc`
- `RiccatiBarrier` (9): `3492f80e8e1de7a4094a5d28f6dd515c57b6d32ed0cf52d942d46b07c872d593`
- `RiccatiLogDerivative` (9): `19e233df3846c1c511ce98543dd2d3d57247f2e6da97c16cb258f75ec640f3d3`
- `RadialLayer` (7): `758b04588c4a327950a3be3e117d70fb14356bcb2391dfd27064c66d77ef5d49`
- `RadialPropagation` (10): `82c485d52574d5f1531c0266384ce44220a6941986971465a10527a4d0791124`
- `RadialStack` (17): `f2ef92e1f4275c97e94a9707b48ee20d3d5c4454bc8ce01abd3a4c11a8fede47`
- `RadialSource` (16): `a5661ed3236ec01a1ae07b4762368ee9725fd95df08b2799237dc83274b6acf4`
- `RadialLoadBounds` (8): `831f58e6b65382396d08ea2bffae0adf6fbefc86265c23f1faf243acf3808d9e`
