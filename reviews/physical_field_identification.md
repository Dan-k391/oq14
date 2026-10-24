# PhysicalFieldIdentification — author verification (modal Sol)

New module `lean/PhysicalFieldIdentification.lean` (1112 lines, imports `RestrictedTEActualPiecewise`,
`RestrictedTEBackgroundOutside`, `ExteriorMaterialOffCarrier`, `SourceRadiatedFlux`, `SourceRadiatedAnnulus`; nothing
existing edited). Source SHA256 `411443D271E04B53846E112D7E541E748B332250AA459BCFE07B4FA55B790E5D`. Final log
`lean/logs/PhysicalFieldIdentification-final.log` SHA256 `8953AB13836095611FDC4C99297AFCC3C9035A6004423A0AC65EF1D120BD5123`,
exit file `lean/logs/PhysicalFieldIdentification-final.exit.log` = 0, object
`.lake/build/lib/lean/PhysicalFieldIdentification.olean` (1505672 bytes). Exit 0, zero warnings, zero errors, no `sorry`;
39 theorems, 39 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`. No docstring line begins with the
words axiom or constant; no theorem has a primed name. Drafts `PhysicalFieldIdentification-check1..18.log`. Author
review only; root independent audit pending.

## Objects (fixed `q, hq : 1 <= q, n, r, ci, dci, b, x : Vec`)

* `physE` = `MaterialField.total (add cs ci) 1 (coreSol x) (electric x)`, `extE` = `ExteriorMaterial.total (add cs ci) 1 X_r
  (coreSol x) (electric x)`, `physH` = `MaterialMaxwell.totalMagnetic (add cs ci) 1 (coreSol x) (magnetic x)`
  (`coreSol x = solution (add cs ci) 1 X_r (fsLin x + fiLin x)`).
* `coreEField`, `coreHField`: `continuousTotalElectric/Magnetic (add cs ci) X_r (electric/magnetic x) (fsLin x + fiLin x)`;
  `coreE x xi = coreEField x (planePoint xi)` and the same for `coreH` hold by `rfl` (`coreE_eq_field`, `coreH_eq_field`).
* `radiatedE q hq n r ci dci b x y` = `genElectric (dataFam q hq0 n) tmFlag polyFam (coeffFam (radCoeff ..)) r y` with
  `radCoeff s j = source ci (inclSolution q hq n s ci dci b x) j` (likewise `radiatedH`, `genMagnetic`).
* `spaceFieldE y` = `coreEField y` if `‖y‖ < R_r`, else `bgFieldE x y + radiatedE y`; `spaceFieldH` likewise.
* `physRegion` = `{y | (‖y‖ < R_r ∧ y ∉ closure dci.carrier) ∨ R_r < ‖y‖}` (measurable).

## Statements

* `core_identification_electric ... hb hci hE x`: for a.e. `y`, `‖y‖ < R_r → y ∉ closure dci.carrier → ∀ i,
  physE y i = coreEField y i` (from `combined_total_electric_ae_off_carrier` and the pointwise `combined_total_electric_eq`
  at the positive distance from the carrier). `core_identification_magnetic`: `physH y i = coreHField y i` for every `y`, and
  `physH (planePoint xi) i = coreH x xi i` for every plane point (the expressions are the same: `rfl`).
* `exterior_identification ... hb0 hcar hL x`: eventually in `r`, for all `y` with `X_r < ‖y‖` and all `i`,
  `extE y i = bgFieldE x y i + radiatedE y i  ∧  physH y i = bgFieldH x y i + radiatedH y i`.
  Proof: `exterior_split_electric/magnetic` (the response of the combined source at a point outside the ball containing
  all sources splits as shell background + free field of the inclusion part + shell response driven by `Ss T Si ui`;
  `block_facts`: `u = r fs + r (Ss T Si ui) + ui`, a.e. split of the source), `extE_eq_coreEField`,
  `backgroundElectric_eq_bgFieldE_exterior`, `backgroundMagnetic_eq_bgFieldH` (`famBackgroundH_eq`), and
  `paired_radiated_series_outside` with the sequence `vSeq` (inclusion solutions cut to zero where their norm exceeds `N`,
  `N` from `solution_bounded_of_coeffs` for the one-element family `{x}`).
* `annulus_identification_electric/magnetic ... hL x`: eventually in `r`, a.e. on `R_r < ‖y‖ ≤ X_r`:
  `physE y i = bgFieldE x y i + radiatedE y i` (resp. `physH`, `bgFieldH`, `radiatedH`). Proof: `scattered_split3_ae` (the `L2`
  scattered field of the combined solution is, a.e. on the ball `X_r`, the sum of the three scattered fields; Newton part by
  linearity in `Lp`, remainder part by `remainder_source_integrable_ae`) resp. `magnetic_split3_ae` (the magnetic response
  splits a.e. on the ball, integrability from `response_integrable_ae`: the truncated locally integrable gradient kernel);
  `famBackground_ae` (shell part), `ExteriorContinuity.electric_ae_exterior` (inclusion part) and the frozen annulus
  identification `paired_annulus_electric_ae`/`paired_annulus_magnetic_ae` (the sum of the shell response driven by the
  inclusion and the free field of the inclusion is `genElectric`/`genMagnetic` a.e. beyond the inner radius).
* `physical_identification_electric ... : ∀ᶠ r, (∀ i, physE =ᵐ[volume.restrict (physRegion ..)] spaceFieldE) ∧ ∀ y, X_r < ‖y‖ →
  ∀ i, extE y i = spaceFieldE y i`.
* `physical_identification_magnetic ... : ∀ᶠ r, (∀ y, ‖y‖ < R_r → ∀ i, physH y i = spaceFieldH y i) ∧ (∀ y, X_r < ‖y‖ → ...) ∧
  ∀ i, physH =ᵐ[volume] spaceFieldH` (the sphere `‖y‖ = R_r` is null).
* `physical_identification ... : ∀ᶠ r, PhysicallyIdentified q hq n r ci dci b x` (the conjunction of the two, `PhysicallyIdentified`
  is the explicit conjunction).
* `deviceFieldsE_eq_space`, `deviceFieldsH_eq_space`: for the concrete device (`concrete_device`), `b < R_r`, and
  `radE n r x xi = radiatedE .. (planePoint xi)` for all `x, xi`: `deviceFieldsE .. (outFieldE q hq.le radE) n r x xi =
  spaceFieldE .. (planePoint xi)` (same for `H`).
* `device_physical_identification r0 y rho chi h R hrho hchi hi q hq`: `∀ᶠ n, ∀ x, ∀ᶠ r, PhysicallyIdentified q hq.le n r (devCoeff ..)
  (devData ..) (max R 1) x` (limiting effective block unit by `partner_limitEffective_isUnit`, carrier in the ball of radius `max R 1`
  by `device_carrier_le`). `device_piecewise_identification` adds `hrho_h : rho < h` and the plane identification of the
  piecewise device fields for every pair of outside radiated `FieldMap`s that are the radiated series at plane points.

## Gaps

1. No hypothesis on the shell annulus remains: it is supplied by the frozen annulus identification of the radiated field.
   The statement is for a fixed input `x` and fixed `n`; `PhysicallyIdentified` is eventually in `r`, the threshold depends on
   `x` (through the bound `N` of the inclusion solutions of that input), `n`.
2. The magnetic total field is identified pointwise on the open core (including the carrier) and the exterior, and almost
   everywhere in the shell annulus; no pointwise statement is made on the annulus.
3. The electric `L2` total field is identified almost everywhere on the open core off the closure of the carrier (the
   statement of `ExteriorMaterialOffCarrier`), not on the closure of the carrier itself.
4. `radE`, `radH` as linear `FieldMap`s (the radiated series at plane points) are not constructed here; `deviceFieldsE_eq_space`
   takes the pointwise relation to the series as a hypothesis (the linear structure and measurability are those of
   `SourceRadiatedAnnulus.genSeries_linear_map`, `radiated_plane_aesm`, used by the channel module).
5. The module does not touch the counting theorem; it is self-contained and independent of the channel module
   `RestrictedTEActualDevice`.
