# ExteriorMaterialOffCarrier — author verification (modal Sol)

New module `lean/ExteriorMaterialOffCarrier.lean` (371 lines, imports `ConicalInteriorResponse` and
`SourcePairedPlaneIdentification`; nothing existing edited). Source SHA256
`28826ABB34D501991F0EBBB93306B2AD0549A5DFA9A3EEF9900BF48B658907C6`. Final log
`lean/logs/ExteriorMaterialOffCarrier-final.log` SHA256 `1467FD0E6ABF19770D187CD853AA1A7F7939DD2BF734342D2166141D65BDFD40`,
exit file `lean/logs/ExteriorMaterialOffCarrier-final.exit.log` = 0, object `.lake/build/lib/lean/ExteriorMaterialOffCarrier.olean`
(644992 bytes). Exit 0, zero warnings, zero errors, no `sorry`; 10 theorems, 10 `#print axioms` reports, all
`[propext, Classical.choice, Quot.sound]`. No docstring line begins with the words axiom or constant. Drafts
`ExteriorMaterialOffCarrier-check1..6.log`. Author review only; root independent audit pending.

## Statements

* `newton_ae_open F ρ hρ hF S hc U hU hi i`: for an L2 vector `F` whose physical coordinates are a.e. the integrable
  sources `ρ j`, which vanish outside `closedBall 0 S` and on the open set `U`, almost every `x ∈ U` satisfies
  `physicalCoordinate (newtonOperator F) i x = ∑ j ∫ y, ρ j y * phiHessian 0 (x - y) i j`.
  Proof: the frozen cut-off kernel pairing of `ConicalInteriorNewton`/`NewtonExteriorResponse` generalized from balls centred
  at the origin to the separation hypothesis `∀ x ∈ tsupport f, ∀ y, ρ y ≠ 0 → δ ≤ ‖x - y‖` (`weakConvolution_sep_pairing`,
  `newton_cutResponse_pairing_sep`), the fundamental lemma on a ball `ball c b` (`newton_ae_cutResponse_ball`, `newton_ae_ball`:
  `ρ` vanishing on `ball c a`, `b < a`, `δ = (a-b)/2`), and a countable cover of `U` by balls `ball c (r c)` with
  `ball c (2 r c) ⊆ U` (`TopologicalSpace.countable_cover_nhdsWithin`, `ae_ball_iff`).
* `electric_ae_open k F ρ hρ hF S hc U hU hi i`: `FieldResponse.electric k F ρ x i = ExteriorContinuity.electric k ρ x i`
  for almost every `x ∈ U` (the Newton part by the previous theorem, the remainder part pointwise: `x ∉ tsupport (ρ j)`,
  `source_excluded_open`, the frozen `ConicalInteriorResponse.source_integrand_integrable`).
* `scattered_ae_off_carrier cs ci b Rin X hbR hRX hcs hci K hK hd u i`: for the shell supported in `Rin ≤ |x| ≤ X`, the
  inclusion vanishing outside `closedBall 0 b` and outside the set `K`, `Disjoint cs ci`, almost every `x` with `‖x‖ < Rin` and
  `x ∉ closure K` satisfies `MaterialField.scattered (add cs ci) 1 u x i = ExteriorContinuity.electric 1 (source (add cs ci) u) x i`.
  This is `scattered_ae_annulus` with the exterior lemma for the inclusion (`b < |x|`) replaced by `electric_ae_open` on the open
  set `(closure K)ᶜ`.
* `combined_total_electric_ae_off_carrier q hq n r ci b hb hci d hE inc fs fi hfi hfs`: for a support data `d` of `ci` (any
  measurable carrier `d.carrier`), almost every `x` with `‖x‖ < (data q hq n r).R` and `x ∉ closure d.carrier`
  satisfies, for all `i`, `MaterialField.total (add shell ci) 1 (solution (add shell ci) 1 X (fs + fi)) inc x i =
  pairedPlaneElectric q hq n r ci (inverse (effectiveBlock ..) (effectiveDatum ..)) (backgroundElectric .. inc fs) x i`.
  It uses `combined_total_electric_eq` (frozen, pointwise at positive distance `ε` from the carrier, obtained here from
  `x ∉ closure d.carrier` by `Metric.mem_closure_iff`).
* `combined_total_electric_ae_restrict`: the set `{x | ‖x‖ < R_r ∧ x ∉ closure d.carrier}` is open and, for each `i`, the
  physical total field is a.e. equal to the assembled plane field with respect to the volume measure restricted to it.
  Every plane point `x0` at positive distance from the carrier lies in this open set, so the identification holds on a
  neighbourhood of `x0` (a.e. in the neighbourhood). With `d := ballSupportData ci b hci` the earlier gap-annulus statement
  `combined_total_electric_ae` is the part `b < |x|` of this set.

## Gaps

1. The identification is almost everywhere in `R^3`; a plane point is covered through the open neighbourhood statement
   (`combined_total_electric_ae_restrict`), not pointwise. This is the content needed to replace the L2 class by the
   continuous representative in plane integrals only after the usual a.e. argument on the plane, which is not part of this
   module.
2. Points of the closure of the carrier (the inclusion material itself) and points `|x| ≥ R_r` are not covered; there the
   total field is not the dyadic integral of the polarization.
3. The carrier of the partner device being a finite union of open balls, the closed set `closure d.carrier` is the union of
   the closed balls (`closure_ball` for positive radii); this identification of the closure is not proved here, the
   statement is for the abstract closure.
4. The magnetic total field needs no such statement (`combined_totalMagnetic_eq` is pointwise at positive distance).
