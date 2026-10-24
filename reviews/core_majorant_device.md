# CoreMajorantDevice — author verification (modal Sol)

New module `lean/CoreMajorantDevice.lean` (345 lines, imports `RestrictedTEActualPiecewise` and `CoreRadiatedMajorant`;
nothing existing edited). Source SHA256 `C94B09B4220965FF2CFB849EA5DF7C0EF80860710E2AD1F7B7E71DC414EFBEDD`. Final log
`lean/logs/CoreMajorantDevice-final.log` SHA256 `3C21E2958F3E267995A9BC9FBB8D2163E96535C8C4648AD518027222EC4C28F3`, exit file
`lean/logs/CoreMajorantDevice-final.exit.log` = 0, object `.lake/build/lib/lean/CoreMajorantDevice.olean` (723864 bytes).
Exit 0, zero warnings, zero errors, no `sorry`; 13 theorems, 13 `#print axioms` reports, all
`[propext, Classical.choice, Quot.sound]`. No docstring line begins with the words axiom or constant. Drafts
`CoreMajorantDevice-check1..6.log`. Author review only; root independent audit pending.

## Statements

* `coreMajorant_device r0 y ρ χ h R hρ hχ hρh hi q hq : RestrictedTEActualPiecewise.CoreMajorant r0 y ρ χ h R hρ hχ hi q hq`
  for the concrete doubled device (positions `fun a l => abovePoint (hpoint r0 y l) (h * a)`, `deviceCoeff`, `deviceData`).
  The extra hypothesis `hρh : ρ < h` is the one already present in `actual_counted_subspaces_of_pieces`
  (it is needed to build `Device`, through `concrete_device`; the structure `CoreMajorant` itself does not mention it).
  A temporary file (not kept) that obtains `r0 := -L`, `y := ysq N L`, `hρh`, `hi`, `hq` from the conclusion of
  `actual_counted_subspaces_of_pieces`, builds `coreMajorant_device (-L) (ysq N L) ρ χ h R hρ hχ hρh hi q hq` and applies the
  final clause to it compiled with exit 0: the hypotheses match exactly, with enclosing radius `b := max R 1`.
* `coreMajorant_of_device hd hq hb0 hRb`: for a `Device p ρ χ R γ`, `q > 1`, any `b > 0` with `R <= b`, eventually in `n`
  (through `partner_limitEffective_isUnit` only): for every orthonormal `B : Fin N -> Vec` there are `C1 ρ1 r1` such that for
  all `r >= r1`, `x` in the span with `physicalPower x = 1`, and `ξ` with `ρ1 <= |ξ| < radius r`,
  `‖crossProduct (coreE .. x ξ) (conjugate (coreH .. x ξ)) 2‖ <= C1 / |ξ|^3`.
* `core_majorant_general q hq n ci dci b η hb0 hcar hη hgap hL N B horth`: the same for an arbitrary inclusion `ci` with
  support data `dci`, carrier in the ball of radius `b` and at height `>= η > 0` from the plane, when the limiting effective
  block is a unit (`hL`). The constants: `ρ1 = max (coreMin q b) ρb + 1` with `ρb` from `background_decomp_unit_sphere`;
  `K` from `core_total_decomp` with zero incident field (free potential and shell reaction field of an inclusion vector
  `u` decompose with constants `3 K ‖u‖` and `K ‖u‖`, independent of `r`, `x`); `U`, `r0` from `solution_bounded_on_sphere`;
  `C1 = 2 K U' (L1' + 3 K U') + 2 (K1' + 3 K U') (L2' + K U')` with `U' = max U 0`, `K1' = max K1 0`, `L1' = max L1 0`,
  `L2' = max L2 0`; the threshold `r1 = max (max ra rb) (max rc r0)` collects the reaction threshold, the inner radius
  `b < R_r` and the unit effective block (`eventually_effective_isUnit`).
* `coreE_eq`, `coreH_eq`: for a `CoreSetup q hq n r ci dci b η`, a unit effective block, `‖ξ‖ < R_r` and
  `planePoint ξ != 0`: `coreE .. x ξ = bgFieldE q hq n r x (planePoint ξ) + pairedPlaneElectric q hq n r ci (inclSolution ..) 0
  (planePoint ξ)`, and the same for `coreH` with `bgFieldH` and `pairedPlaneMagnetic`. From `combined_total_electric_eq` /
  `combined_total_magnetic_eq` (the effective datum in `Ring.inverse` form is the definition of `inclSolution`; the lemma
  `inclPart_eq_inclSolution` is not needed) and the background identification below.
* `backgroundElectric_eq_bgFieldE`, `backgroundMagnetic_eq_bgFieldH`: for `y != 0`, `‖y‖ < R_r`, the continuous shell
  backgrounds equal `bgFieldE`, `bgFieldH` (from `backgroundElectric_eq_core` / `backgroundMagnetic_eq_core` and
  `shell_te_core`, `bgFieldH_core`).
* `bgFieldH_core` (the missing magnetic counterpart of `shell_te_core`, stated for `bgFieldH`, which is
  `famBackgroundH` of the physical TE stack): for `x != 0`, `‖x‖ <= radius r`, every coordinate `i`,
  `bgFieldH q hq n r A x i = RestrictedTEPlaneLocal.magnetic (scaledCoeff A (trans q hq n r)) x i`.
  Proof: `famBackgroundH` is minus the TM-structure electric background of the TE data (`bgFieldH_apply`); by
  `backgroundElectric_core` it is `transmission/2` times the regular profile `SolidMaxwellProfiles.electric`; the TE
  magnetic field of a wave is `-I` times that profile (`teMagnetic_wave`), and `teCoeff = coefficient * I`;
  the regular TE magnetic field of the rescaled vector is the finite sum over the support (`magnetic_scaledCoeff_eq`),
  the transmission of the physical TE stack being the stack transmission (`physicalTE_transmission`).
* `flux_arith`: elementary monotonicity of the flux constant in the norm `‖u‖` of the inclusion solution.

## Gaps

1. The majorant is for the cut-off free core fields `coreE`, `coreH` exactly as in the structure `CoreMajorant`; the
   outside fields and their decomposition (`OutsideDecomposition`) are not part of this module.
2. `C1`, `ρ1`, `r1` depend on `n` and `B` (through `ρb, K1, L1, L2` of the background, `U`, `r0`), as the structure requires.
3. The statement is for the unit-power sphere of the span, via the linearity of the background in the input
   (`background_decomp_unit_sphere`) and the uniform bound of the inclusion solution (`solution_bounded_on_sphere`); no
   estimate on the inclusion solution is proved here beyond that frozen bound, whose hypothesis is the unit limiting effective
   block (`partner_limitEffective_isUnit`, eventually in `n`).
4. Not used: `core_flux_majorant_te` (single coefficient vector), the untracked module `RestrictedTEBackgroundOutside`.
