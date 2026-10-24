import RestrictedTEParityInstance
import SourceRadiatedAnnulus

/-! The counted-subspace theorem of the physical paired device, with no field hypotheses.

`RestrictedTEParityInstance.actual_counted_subspaces_of_radiated` leaves two hypotheses on abstract linear
radiated plane fields `radE`, `radH`: measurable coordinates and the uniform radial/tangential decomposition.  This
module supplies them for the fields of the actual device.

* `radElec`, `radMag`, `radElecMap`, `radMagMap`: the radiated plane fields at shell index `r` are the all-degree
  layered mode series (`SourceRadiatedFlux.genElectric`, `genMagnetic`) of the moments of the source of the
  inclusion solution `inclSolution` of the input, at the plane point, for `r` beyond the threshold `radThreshold` and
  `radius r < ‖ξ‖`, and zero otherwise.  They are linear in the input (`genSeries_linear_map` applied to the linear map
  `inclLin`; `radElec_add`, `radElec_smul`), so they are `FieldMap`s.
* `radElec_meas`, `radMag_meas`: the coordinates are almost everywhere strongly measurable on the plane
  (`radiated_plane_aesm` on the open set `{radius r < ‖ξ‖}`, zero elsewhere; the circle is null).
* `rad_decomp`: if the limiting effective block is a unit, then for every orthonormal family the radiated fields
  decompose uniformly in `r` on the unit-power sphere of its span (`radiated_decomp_outside_of_norm_bound`, with the
  bound of the inclusion solution from `solution_bounded_on_sphere`, the inclusion vectors being modified below the
  bounded range), and the fields vanish on the circle and below the threshold.
* `devRadE`, `devRadH`, `devRad_meas`, `devRad_hrad`: the same for the concrete doubled device (enclosing radius
  `max R 1`; the limiting block is a unit for all large `n` by `partner_limitEffective_isUnit`).
* `actual_counted_subspaces_device`: `actual_counted_subspaces_of_radiated` with `radE := devRadE`,
  `radH := devRadH`: no field hypothesis is left.  The statement is about the piecewise device fields (the cut-off core
  fields inside the disk of radius `radius r`, `outFieldE`, `outFieldH` beyond). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualDevice
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Vec := OQ14.RestrictedTEActualCore.Vec
abbrev Sp := FourierL2.Space

/-! ### The radiated plane fields of the device -/

section Radiated
open OQ14.SourceRadiatedFlux OQ14.RestrictedTEActualPiecewise

/-- The inner degree scale `B = degreeScale 2 b` of the radiated series of an inclusion in the ball of radius `b`. -/
def innerB (b : ℝ) : ℝ := HarmonicSpatialMajorant.degreeScale 2 b

/-- The inner scale `s0 = B + 1` at which the series moments are normalized. -/
def innerS0 (b : ℝ) : ℝ := HarmonicSpatialMajorant.degreeScale 2 b + 1

/-- The shell index from which the radiated series of the device with enclosing radius `b` is controlled. -/
def radThreshold (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (b : ℝ) : ℕ :=
  max (BarrierDegreeDecomp.s1pair q (zero_lt_one.trans_le hq) n (innerS0 b))
    (BarrierDegreeDecomp.s1pair q (zero_lt_one.trans_le hq) n 1)

/-- The radiated electric field of the inclusion solution at shell index `r`: the generalized layered mode
series of the moments of the source of the inclusion solution `inclSolution` of the input `x`, at the plane point
`ξ`, for `r` beyond the threshold and `radius r < ‖ξ‖`; zero otherwise. -/
def radElec (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    Maxwell.Vector :=
  if radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖ then
    genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
      (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r
      (MaxwellPlaneTail.planePoint ξ)
  else 0

/-- The radiated magnetic field of the inclusion solution (the magnetic series). -/
def radMag (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    Maxwell.Vector :=
  if radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖ then
    genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
      (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r
      (MaxwellPlaneTail.planePoint ξ)
  else 0

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b) (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)

include hcar

theorem hci_of_carrier : ∀ y : Sp, y ∉ closedBall (0 : Sp) b → ci.value (VectorFourier.coordinateMap y) = 0 :=
  SourcePairedReduction.inclusion_vanish ci dci b hcar

include hb0

/-- Linearity of the electric series in the input, at a point outside the inner radius. -/
theorem genE_lin (r : ℕ) (hr : radThreshold q hq n b ≤ r) (y : Sp) (hy : RadialPhaseLimit.radius r < ‖y‖)
    (x w : Vec) (α β : ℂ) :
    genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b (α • x + β • w)) j)) r y =
      α • genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r y +
      β • genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b w) j)) r y :=
  (SourceRadiatedAnnulus.genSeries_linear_map (inclLin q hq n r ci dci b) q (zero_lt_one.trans_le hq) hq n ci b
    (HarmonicSpatialMajorant.degreeScale 2 b) (HarmonicSpatialMajorant.degreeScale 2 b + 1) hb0.le
    (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) le_rfl (lt_add_one _)
    (lt_of_le_of_lt (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) (lt_add_one _))
    (hci_of_carrier ci dci b hcar) r hr y hy x w α β).1

/-- Linearity of the magnetic series in the input. -/
theorem genH_lin (r : ℕ) (hr : radThreshold q hq n b ≤ r) (y : Sp) (hy : RadialPhaseLimit.radius r < ‖y‖)
    (x w : Vec) (α β : ℂ) :
    genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b (α • x + β • w)) j)) r y =
      α • genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r y +
      β • genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b w) j)) r y :=
  (SourceRadiatedAnnulus.genSeries_linear_map (inclLin q hq n r ci dci b) q (zero_lt_one.trans_le hq) hq n ci b
    (HarmonicSpatialMajorant.degreeScale 2 b) (HarmonicSpatialMajorant.degreeScale 2 b + 1) hb0.le
    (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) le_rfl (lt_add_one _)
    (lt_of_le_of_lt (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) (lt_add_one _))
    (hci_of_carrier ci dci b hcar) r hr y hy x w α β).2

theorem radElec_add (r : ℕ) (x w : Vec) (ξ : PlaneInverseCube.Plane) :
    radElec q hq n ci dci b r (x + w) ξ = radElec q hq n ci dci b r x ξ + radElec q hq n ci dci b r w ξ := by
  unfold radElec
  by_cases hc : radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖
  · simp only [if_pos hc]
    have hy : RadialPhaseLimit.radius r < ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hc.2
    have h := genE_lin q hq n ci dci b hb0 hcar r hc.1 _ hy x w 1 1
    simpa only [one_smul] using h
  · simp only [if_neg hc, add_zero]

theorem radElec_smul (r : ℕ) (z : ℂ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    radElec q hq n ci dci b r (z • x) ξ = z • radElec q hq n ci dci b r x ξ := by
  unfold radElec
  by_cases hc : radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖
  · simp only [if_pos hc]
    have hy : RadialPhaseLimit.radius r < ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hc.2
    have h := genE_lin q hq n ci dci b hb0 hcar r hc.1 _ hy x 0 z 0
    simpa only [smul_zero, add_zero, zero_smul] using h
  · simp only [if_neg hc, smul_zero]

theorem radMag_add (r : ℕ) (x w : Vec) (ξ : PlaneInverseCube.Plane) :
    radMag q hq n ci dci b r (x + w) ξ = radMag q hq n ci dci b r x ξ + radMag q hq n ci dci b r w ξ := by
  unfold radMag
  by_cases hc : radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖
  · simp only [if_pos hc]
    have hy : RadialPhaseLimit.radius r < ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hc.2
    have h := genH_lin q hq n ci dci b hb0 hcar r hc.1 _ hy x w 1 1
    simpa only [one_smul] using h
  · simp only [if_neg hc, add_zero]

theorem radMag_smul (r : ℕ) (z : ℂ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    radMag q hq n ci dci b r (z • x) ξ = z • radMag q hq n ci dci b r x ξ := by
  unfold radMag
  by_cases hc : radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖
  · simp only [if_pos hc]
    have hy : RadialPhaseLimit.radius r < ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hc.2
    have h := genH_lin q hq n ci dci b hb0 hcar r hc.1 _ hy x 0 z 0
    simpa only [smul_zero, add_zero, zero_smul] using h
  · simp only [if_neg hc, smul_zero]

/-- The radiated electric plane field of the device at shell index `r`, linear in the input. -/
def radElecMap (r : ℕ) : FieldMap where
  toFun x ξ := radElec q hq n ci dci b r x ξ
  map_add' x w := by
    funext ξ
    exact radElec_add q hq n ci dci b hb0 hcar r x w ξ
  map_smul' z x := by
    funext ξ
    exact radElec_smul q hq n ci dci b hb0 hcar r z x ξ

/-- The radiated magnetic plane field of the device at shell index `r`, linear in the input. -/
def radMagMap (r : ℕ) : FieldMap where
  toFun x ξ := radMag q hq n ci dci b r x ξ
  map_add' x w := by
    funext ξ
    exact radMag_add q hq n ci dci b hb0 hcar r x w ξ
  map_smul' z x := by
    funext ξ
    exact radMag_smul q hq n ci dci b hb0 hcar r z x ξ

theorem radElecMap_apply (r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    radElecMap q hq n ci dci b hb0 hcar r x ξ = radElec q hq n ci dci b r x ξ := rfl

theorem radMagMap_apply (r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    radMagMap q hq n ci dci b hb0 hcar r x ξ = radMag q hq n ci dci b r x ξ := rfl

end Radiated

/-! ### Measurability and the radial/tangential decomposition of the radiated plane fields -/

section Congr
open OQ14.SourceRadiatedFlux

/-- Coefficient families that agree at the evaluation index give the same series. -/
theorem genElectric_coeff_congr (D : ModeIdx → ℕ → OQ14.SourceRadialSystem.Data) (tm : ModeIdx → Bool)
    (P : ModeIdx → HarmonicPolynomial.Poly) (ρ₁ ρ₂ : ℕ → Fin 3 → Sp → ℂ) (r : ℕ) (h : ρ₁ r = ρ₂ r) (y : Sp) :
    genElectric D tm P (coeffFam ρ₁) r y = genElectric D tm P (coeffFam ρ₂) r y := by
  have hc : coeffFam ρ₁ r = coeffFam ρ₂ r := by
    funext i
    cases i <;> simp [coeffFam, h]
  unfold genElectric
  rw [hc]

theorem genMagnetic_coeff_congr (D : ModeIdx → ℕ → OQ14.SourceRadialSystem.Data) (tm : ModeIdx → Bool)
    (P : ModeIdx → HarmonicPolynomial.Poly) (ρ₁ ρ₂ : ℕ → Fin 3 → Sp → ℂ) (r : ℕ) (h : ρ₁ r = ρ₂ r) (y : Sp) :
    genMagnetic D tm P (coeffFam ρ₁) r y = genMagnetic D tm P (coeffFam ρ₂) r y := by
  have hc : coeffFam ρ₁ r = coeffFam ρ₂ r := by
    funext i
    cases i <;> simp [coeffFam, h]
  unfold genMagnetic
  rw [hc]

end Congr

section Properties
open OQ14.SourceRadiatedFlux OQ14.RestrictedTEActualPiecewise

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b) (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
include hb0 hcar

/-- **Plane measurability of the radiated electric field.**  Every coordinate of `radElec` is almost everywhere
strongly measurable on the plane: it is the indicator of the open set `{radius r < ‖ξ‖}` (the circle is null) of the
series, which is measurable by `radiated_plane_aesm`, and zero for `r` below the threshold. -/
theorem radElec_meas (r : ℕ) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : PlaneInverseCube.Plane => radElec q hq n ci dci b r x ξ i) volume := by
  by_cases hth : radThreshold q hq n b ≤ r
  · have hci := hci_of_carrier ci dci b hcar
    have hS : MeasurableSet {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius r < ‖ξ‖} :=
      (isOpen_lt continuous_const continuous_norm).measurableSet
    have hg := SourceRadiatedAnnulus.radiated_plane_aesm q (zero_lt_one.trans_le hq) hq n b
      (HarmonicSpatialMajorant.degreeScale 2 b) (HarmonicSpatialMajorant.degreeScale 2 b + 1)
      (3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Sp) b))) *
        ‖inclSolution q hq n r ci dci b x‖)) hb0.le (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) le_rfl
      (lt_add_one _) (lt_of_le_of_lt (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) (lt_add_one _))
      (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)
      (fun _ j => DynamicVolume.source_integrable ci _ b hci j)
      (fun _ j y hy => DynamicVolume.source_zero ci _ b hci j y (by
        rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy))
      (fun _ => SourceRadiatedFlux.mass_le_norm ci b hci _) r hth i
    have e : (fun ξ : PlaneInverseCube.Plane => radElec q hq n ci dci b r x ξ i) =
        Set.indicator {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius r < ‖ξ‖}
          (fun ξ => genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
            (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r
            (MaxwellPlaneTail.planePoint ξ) i) := by
      funext ξ
      unfold radElec
      by_cases hlt : RadialPhaseLimit.radius r < ‖ξ‖
      · rw [if_pos ⟨hth, hlt⟩, Set.indicator_of_mem (show ξ ∈ {ξ : PlaneInverseCube.Plane |
          RadialPhaseLimit.radius r < ‖ξ‖} from hlt)]
      · rw [if_neg (fun h => hlt h.2), Set.indicator_of_not_mem (show ξ ∉ {ξ : PlaneInverseCube.Plane |
          RadialPhaseLimit.radius r < ‖ξ‖} from hlt)]
        rfl
    rw [e, aestronglyMeasurable_indicator_iff hS]
    exact hg.1.mono_measure (Measure.restrict_mono (fun ξ (h : RadialPhaseLimit.radius r < ‖ξ‖) => h.le) le_rfl)
  · have e : (fun ξ : PlaneInverseCube.Plane => radElec q hq n ci dci b r x ξ i) = fun _ => 0 := by
      funext ξ
      unfold radElec
      rw [if_neg (fun h => hth h.1)]
      rfl
    rw [e]
    exact aestronglyMeasurable_const

/-- **Plane measurability of the radiated magnetic field.** -/
theorem radMag_meas (r : ℕ) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : PlaneInverseCube.Plane => radMag q hq n ci dci b r x ξ i) volume := by
  by_cases hth : radThreshold q hq n b ≤ r
  · have hci := hci_of_carrier ci dci b hcar
    have hS : MeasurableSet {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius r < ‖ξ‖} :=
      (isOpen_lt continuous_const continuous_norm).measurableSet
    have hg := SourceRadiatedAnnulus.radiated_plane_aesm q (zero_lt_one.trans_le hq) hq n b
      (HarmonicSpatialMajorant.degreeScale 2 b) (HarmonicSpatialMajorant.degreeScale 2 b + 1)
      (3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Sp) b))) *
        ‖inclSolution q hq n r ci dci b x‖)) hb0.le (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) le_rfl
      (lt_add_one _) (lt_of_le_of_lt (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) (lt_add_one _))
      (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)
      (fun _ j => DynamicVolume.source_integrable ci _ b hci j)
      (fun _ j y hy => DynamicVolume.source_zero ci _ b hci j y (by
        rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy))
      (fun _ => SourceRadiatedFlux.mass_le_norm ci b hci _) r hth i
    have e : (fun ξ : PlaneInverseCube.Plane => radMag q hq n ci dci b r x ξ i) =
        Set.indicator {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius r < ‖ξ‖}
          (fun ξ => genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
            (coeffFam (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)) r
            (MaxwellPlaneTail.planePoint ξ) i) := by
      funext ξ
      unfold radMag
      by_cases hlt : RadialPhaseLimit.radius r < ‖ξ‖
      · rw [if_pos ⟨hth, hlt⟩, Set.indicator_of_mem (show ξ ∈ {ξ : PlaneInverseCube.Plane |
          RadialPhaseLimit.radius r < ‖ξ‖} from hlt)]
      · rw [if_neg (fun h => hlt h.2), Set.indicator_of_not_mem (show ξ ∉ {ξ : PlaneInverseCube.Plane |
          RadialPhaseLimit.radius r < ‖ξ‖} from hlt)]
        rfl
    rw [e, aestronglyMeasurable_indicator_iff hS]
    exact hg.2.mono_measure (Measure.restrict_mono (fun ξ (h : RadialPhaseLimit.radius r < ‖ξ‖) => h.le) le_rfl)
  · have e : (fun ξ : PlaneInverseCube.Plane => radMag q hq n ci dci b r x ξ i) = fun _ => 0 := by
      funext ξ
      unfold radMag
      rw [if_neg (fun h => hth h.1)]
      rfl
    rw [e]
    exact aestronglyMeasurable_const

/-- **The radiated decomposition of the device.**  If the limiting effective block is a unit, then for every
orthonormal family there are constants and a shell index such that for `r ≥ r2`, every unit-power vector of the
span and every plane point outside (or on) the disk of radius `radius r`, the radiated electric and magnetic plane
fields decompose into a part orthogonal to the position of size `K1/‖ξ‖` (`L1/‖ξ‖`) and a radial part of size
`K2/‖ξ‖²` (`L2/‖ξ‖²`).  The constants come from the mass bound of the inclusion solution on the unit-power
sphere (`solution_bounded_on_sphere`); on the circle and below the threshold the fields are zero. -/
theorem rad_decomp (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0))
    (N' : Nat) (B' : Fin N' → Vec) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B' k))) :
    ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B'),
      RestrictedTEIncoming.physicalPower x = 1 → ∀ ξ : PlaneInverseCube.Plane,
        RadialPhaseLimit.radius r ≤ ‖ξ‖ →
          OQ14.SourceRemotePlaneBand.Decomp K1 K2 (radElec q hq n ci dci b r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
            OQ14.SourceRemotePlaneBand.Decomp L1 L2 (radMag q hq n ci dci b r x ξ) (MaxwellPlaneTail.planePoint ξ) := by
  have hci := hci_of_carrier ci dci b hcar
  obtain ⟨U, rU, hU⟩ := solution_bounded_on_sphere q hq n ci dci b hb0 hcar hL B' horth
  let κ := {x : Vec // x ∈ Submodule.span ℂ (Set.range B') ∧ RestrictedTEIncoming.physicalPower x = 1}
  let v : κ → ℕ → SourceRadiatedSeries.VectorL2 := fun k s => inclSolution q hq n (max s rU) ci dci b k.1
  have hN : ∀ k s, ‖v k s‖ ≤ max U 0 := fun k s =>
    (hU (max s rU) (le_max_right _ _) k.1 k.2.1 k.2.2).trans (le_max_left _ _)
  obtain ⟨K1, K2, L1, L2, s1, hK1, hK2, hL1, hL2, hdec⟩ :=
    SourceRadiatedAnnulus.radiated_decomp_outside_of_norm_bound q (zero_lt_one.trans_le hq) hq n ci b
      (HarmonicSpatialMajorant.degreeScale 2 b) (HarmonicSpatialMajorant.degreeScale 2 b + 1) (max U 0) hb0.le
      (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) le_rfl (lt_add_one _)
      (lt_of_le_of_lt (HarmonicSpatialMajorant.degreeScale_nonnegative 2 b) (lt_add_one _)) v hci hN
  refine ⟨K1, K2, L1, L2, max (max s1 rU) (radThreshold q hq n b), fun r hr x hx hp ξ hξ => ?_⟩
  have hr1 : s1 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hr2 : rU ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hr3 : radThreshold q hq n b ≤ r := (le_max_right _ _).trans hr
  have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le (RadialPhaseLimit.radius_pos r) hξ
  have hy0 : MaxwellPlaneTail.planePoint ξ ≠ 0 :=
    norm_pos_iff.mp (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξpos)
  by_cases hlt : RadialPhaseLimit.radius r < ‖ξ‖
  · have hy : RadialPhaseLimit.radius r < ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hlt
    obtain ⟨d1, d2⟩ := hdec ⟨x, hx, hp⟩ r hr1 (MaxwellPlaneTail.planePoint ξ) hy
    have hvr : v ⟨x, hx, hp⟩ r = inclSolution q hq n r ci dci b x := by
      show inclSolution q hq n (max r rU) ci dci b x = _
      rw [max_eq_left hr2]
    refine ⟨?_, ?_⟩
    · unfold radElec
      rw [if_pos ⟨hr3, hlt⟩]
      have e1 := genElectric_coeff_congr (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)
        (fun s j => DynamicVolume.source ci (v ⟨x, hx, hp⟩ s) j) r (by funext j; simp only [hvr])
        (MaxwellPlaneTail.planePoint ξ)
      rw [e1]
      exact d1
    · unfold radMag
      rw [if_pos ⟨hr3, hlt⟩]
      have e2 := genMagnetic_coeff_congr (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
        (fun _ j => DynamicVolume.source ci (inclSolution q hq n r ci dci b x) j)
        (fun s j => DynamicVolume.source ci (v ⟨x, hx, hp⟩ s) j) r (by funext j; simp only [hvr])
        (MaxwellPlaneTail.planePoint ξ)
      rw [e2]
      exact d2
  · refine ⟨?_, ?_⟩
    · unfold radElec
      rw [if_neg (fun h => hlt h.2)]
      exact OQ14.BarrierDegreeFluxConstants.decomp_mono hy0 (OQ14.SourceRemotePlaneBand.decomp_zero _) hK1 hK2
    · unfold radMag
      rw [if_neg (fun h => hlt h.2)]
      exact OQ14.BarrierDegreeFluxConstants.decomp_mono hy0 (OQ14.SourceRemotePlaneBand.decomp_zero _) hL1 hL2

end Properties

/-! ### The radiated fields of the concrete doubled device and the final theorem -/

section Device
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEActualPiecewise

/-- The radiated electric plane fields of the concrete doubled device (enclosing radius `max R 1`): the series of
the moments of the inclusion solution of the combined device, linear in the input. -/
def devRadE {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) {q : ℝ} (hq : 1 < q) :
    ℕ → ℕ → FieldMap :=
  fun n r => radElecMap q hq.le n
    (deviceCoeff (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
    (deviceData (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) (max R 1)
    (lt_of_lt_of_le one_pos (le_max_right R 1))
    (device_carrier_le (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le (le_max_left R 1)
      hi q hq n) r

/-- The radiated magnetic plane fields of the concrete doubled device. -/
def devRadH {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) {q : ℝ} (hq : 1 < q) :
    ℕ → ℕ → FieldMap :=
  fun n r => radMagMap q hq.le n
    (deviceCoeff (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
    (deviceData (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) (max R 1)
    (lt_of_lt_of_le one_pos (le_max_right R 1))
    (device_carrier_le (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le (le_max_left R 1)
      hi q hq n) r

/-- The radiated fields of the device have almost everywhere strongly measurable coordinates. -/
theorem devRad_meas {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) {q : ℝ} (hq : 1 < q)
    (n r : ℕ) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => devRadE r0 y ρ χ h R hρ hχ hi hq n r x ξ i) volume ∧
      AEStronglyMeasurable (fun ξ => devRadH r0 y ρ χ h R hρ hχ hi hq n r x ξ i) volume :=
  ⟨radElec_meas q hq.le n _ _ (max R 1) (lt_of_lt_of_le one_pos (le_max_right R 1))
      (device_carrier_le (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
        (le_max_left R 1) hi q hq n) r x i,
    radMag_meas q hq.le n _ _ (max R 1) (lt_of_lt_of_le one_pos (le_max_right R 1))
      (device_carrier_le (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
        (le_max_left R 1) hi q hq n) r x i⟩

/-- **The radiated decomposition `hrad` of the device**, for all large gain indices (the limiting effective block
of the doubled device is a unit, `partner_limitEffective_isUnit`). -/
theorem devRad_hrad {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) {q : ℝ} (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ (N' : Nat) (B : Fin N' → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
        ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
            OQ14.SourceRemotePlaneBand.Decomp K1 K2 (devRadE r0 y ρ χ h R hρ hχ hi hq n r x ξ)
              (MaxwellPlaneTail.planePoint ξ) ∧
            OQ14.SourceRemotePlaneBand.Decomp L1 L2 (devRadH r0 y ρ χ h R hρ hχ hi hq n r x ξ)
              (MaxwellPlaneTail.planePoint ξ) := by
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  filter_upwards [partner_limitEffective_isUnit (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1)
    hρ hχ.le hb0 (le_max_left R 1) hi q hq] with n hL
  intro N' B horth
  exact rad_decomp q hq.le n _ _ (max R 1) hb0
    (device_carrier_le (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
      (le_max_left R 1) hi q hq n) hL N' B horth

/-- **The counted-subspace theorem of the physical device, with no field hypotheses.**  For every `ε₊ > 1`, `N`,
thresholds `0 < η < δ`, `τ ≤ 1` and half-side `L > 0` there are the device parameters of the square theorem and an
orthonormal family `A` of `N` physical inputs (permittivity of the paired device in `[1, ε₊]`) such that, eventually
in the gain index `n` and then in the shell index `r`, the span of `A` is a counted subspace through the square
`Dsq L` for the plane flux of the assembled device fields: the cut-off core fields inside the disk of radius
`radius r`, and beyond it the TE background plus the radiated series of the inclusion solution
(`devRadE`, `devRadH`).  The only inputs are the audited modules: the series fields are linear, measurable and satisfy
the uniform radial/tangential decomposition (`devRad_meas`, `devRad_hrad`), the core majorant is
`coreMajorant_device`, and the twist identity is the modal phase. -/
theorem actual_counted_subspaces_device (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∃ _ : max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R,
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ∧
          MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ≤ εp) ∧
      ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
        IsCounted (Submodule.span ℂ (Set.range A))
          (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
            (le_max_left R 1) hi q hq n r)
          (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
            (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r)
            (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r) a))
          (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
            (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r)
            (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    OQ14.RestrictedTEParityInstance.actual_counted_subspaces_of_radiated εp hεp N η δ hη hηδ τ hτ L hL
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  exact h6 (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq) (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)
    (fun n r x i => devRad_meas (-L) (ysq N L) ρ χ h R hρ hχ hi hq n r x i)
    (devRad_hrad (-L) (ysq N L) ρ χ h R hρ hχ hi hq)

end Device

end OQ14.RestrictedTEActualDevice

#print axioms OQ14.RestrictedTEActualDevice.hci_of_carrier
#print axioms OQ14.RestrictedTEActualDevice.genE_lin
#print axioms OQ14.RestrictedTEActualDevice.genH_lin
#print axioms OQ14.RestrictedTEActualDevice.radElec_add
#print axioms OQ14.RestrictedTEActualDevice.radElec_smul
#print axioms OQ14.RestrictedTEActualDevice.radMag_add
#print axioms OQ14.RestrictedTEActualDevice.radMag_smul
#print axioms OQ14.RestrictedTEActualDevice.radElecMap_apply
#print axioms OQ14.RestrictedTEActualDevice.radMagMap_apply
#print axioms OQ14.RestrictedTEActualDevice.genElectric_coeff_congr
#print axioms OQ14.RestrictedTEActualDevice.genMagnetic_coeff_congr
#print axioms OQ14.RestrictedTEActualDevice.radElec_meas
#print axioms OQ14.RestrictedTEActualDevice.radMag_meas
#print axioms OQ14.RestrictedTEActualDevice.rad_decomp
#print axioms OQ14.RestrictedTEActualDevice.devRad_meas
#print axioms OQ14.RestrictedTEActualDevice.devRad_hrad
#print axioms OQ14.RestrictedTEActualDevice.actual_counted_subspaces_device
