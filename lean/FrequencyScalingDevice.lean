import FrequencyScalingMaxwell
import FrequencyScalingFlux
import PhysicalDeviceFields

/-! # Frequency scaling of the concrete doubled dielectric device

This module applies the dilation lemmas of `FrequencyScalingMaxwell` and `FrequencyScalingFlux` to the concrete
doubled dielectric device of the channel branch.

* `combined_testMaxwell`, `device_testMaxwell`: the physical fields `physE`, `physH` of the combined
  shell-plus-inclusion solution satisfy the weak frequency-one dielectric Maxwell system for the combined
  coefficient `ShellInclusionVolume.add shell ci`, whenever the combined volume block is a unit (and, for the
  concrete device, eventually in the gain index `n` and the shell index `r`).
* `device_testMaxwell_scaled`: the dilated fields `scaleField k physE`, `scaleField k physH` satisfy the weak
  frequency-`k` system with the dilated coefficient `scaleCoeff k (pairedCoeff ..)`.
* `PhysicallyIdentifiedAt`, `physicallyIdentified_scale`: the physical identification transports along the
  dilation, with the radii divided by `k`.
* `planePoint_smul`, `device_fields_scaled`: the dilated piecewise plane fields `scaleMap k deviceFieldsE`,
  `scaleMap k deviceFieldsH` are plane values of the dilated space fields at every plane point off the dilated
  circle `‖ξ‖ = radius r / k`, together with the dilated identification and the dilated Maxwell system. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace OQ14.FrequencyScalingDevice

open Filter Topology MeasureTheory Metric OQ14.MaterialMaxwell OQ14.FrequencyScalingMaxwell
  OQ14.FrequencyScalingFlux OQ14.PhysicalFieldIdentification
open scoped Topology

abbrev Vec := OQ14.RestrictedTEActualCore.Vec
abbrev VectorL2 := VectorFourier.VectorL2

/-! ### The weak Maxwell system of the physical fields -/

/-- **The physical fields of the combined solution solve the weak frequency-one dielectric Maxwell system.**
If the combined shell-plus-inclusion volume block is a unit, the physical fields `physE`, `physH` satisfy
`TestMaxwell 1` with the dielectric of the combined coefficient. -/
theorem combined_testMaxwell (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : b < Rof q hq n r)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hC : IsUnit (DynamicVolume.volumeBlock (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)))
    (x : Vec) :
    TestMaxwell 1 (dielectric (ShellInclusionVolume.add (shellOf q hq n r) ci))
      (physE q hq n r ci dci x) (physH q hq n r ci dci x) := by
  have hci := SourcePairedReduction.inclusion_vanish ci dci b hcar
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hsupp := add_support_X q hq n r ci b hb hci
  have hsol : DynamicVolume.volumeBlock (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)
      (RestrictedTEActualCore.coreSol q hq n r ci dci x) =
      RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x :=
    congrArg (fun L : VectorL2 →L[ℂ] VectorL2 =>
      L (RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x))
      (Ring.mul_inverse_cancel _ hC)
  exact MaterialMaxwell.volume_solution_testMaxwell _ 1 (Xof q hq n r) _ _
    (RestrictedTEPlaneLocal.electric x) (RestrictedTEPlaneLocal.magnetic x) hsupp
    (SourcePairedPlaneIdentification.isDatum_add _ _ hd _ _ _
      (RestrictedTEActualCore.fs_isDatum q hq n r x) (RestrictedTEActualCore.fi_isDatum ci dci x))
    hsol (fun i => (RestrictedTEMaterial.electric_smooth x i).continuous.locallyIntegrable)
    (fun i => (RestrictedTEMaterial.magnetic_smooth x i).continuous.locallyIntegrable)
    (RestrictedTEMaterial.testMaxwell x)

/-- **The concrete doubled device solves the weak frequency-one dielectric Maxwell system.**  Eventually in the
gain index `n`, for every input `x`, and eventually in the shell index `r`, the physical fields of the combined
shell-plus-inclusion solution satisfy `TestMaxwell 1` with the dielectric of the paired coefficient. -/
theorem device_testMaxwell {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vec, ∀ᶠ r : ℕ in atTop,
      TestMaxwell 1 (dielectric (OQ14.ChannelMaterialThroughput.pairedCoeff q hq.le n r
          (devCoeff r0 y ρ χ h hχ q n)))
        (physE q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) x)
        (physH q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) x) := by
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  filter_upwards [RestrictedTEPartnerSmallness.partner_limitEffective_isUnit (devPos r0 y h) ρ χ R (max R 1)
    hρ hχ.le hb0 (le_max_left R 1) hi q hq] with n hL
  intro x
  have hcar := RestrictedTEActualCounting.device_carrier_le (devPos r0 y h) ρ χ R (max R 1) hρ hχ.le
    (le_max_left R 1) hi q hq n
  filter_upwards [SourcePairedReduction.eventually_combined_isUnit q hq.le n (devCoeff r0 y ρ χ h hχ q n)
    (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) hb0 hcar hL,
    SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1)] with r hC hbr
  exact combined_testMaxwell q hq.le n r _ _ (max R 1) hbr hcar hC x

/-- **The dilated concrete doubled device solves the weak frequency-`k` dielectric Maxwell system.**  The dilated
and amplified physical fields `scaleField k physE`, `scaleField k physH` satisfy `TestMaxwell k` with the dilated
dielectric `scaleCoeff k (pairedCoeff ..)`. -/
theorem device_testMaxwell_scaled (k : ℝ) (hk : 0 < k) {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ)
    (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vec, ∀ᶠ r : ℕ in atTop,
      TestMaxwell k (dielectric (scaleCoeff k (OQ14.ChannelMaterialThroughput.pairedCoeff q hq.le n r
          (devCoeff r0 y ρ χ h hχ q n))))
        (scaleField k (physE q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
          (devData r0 y ρ χ h R hρ hχ hi q hq n) x))
        (scaleField k (physH q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
          (devData r0 y ρ χ h R hρ hχ hi q hq n) x)) := by
  filter_upwards [device_testMaxwell r0 y ρ χ h R hρ hχ hi q hq] with n hn
  intro x
  filter_upwards [hn x] with r hM
  exact testMaxwell_scaleCoeff k hk _ _ _ hM

/-! ### The dilated physical identification -/

/-- The dilated form of `PhysicallyIdentified`: the dilated physical fields are identified with the dilated space
fields on the dilated region (the region preimage under `y ↦ k y`, the radii divided by `k`). -/
def PhysicallyIdentifiedAt (k : ℝ) (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) : Prop :=
  ((∀ i : Fin 3, (fun y => scaleField k (physE q hq n r ci dci x) y i)
        =ᵐ[volume.restrict ((fun y : Maxwell.Space => k • y) ⁻¹' physRegion q hq n r dci)]
      fun y => scaleField k (spaceFieldE q hq n r ci dci b x) y i) ∧
    ∀ y : Maxwell.Space, Xof q hq n r / k < ‖y‖ → ∀ i : Fin 3,
      scaleField k (extE q hq n r ci dci x) y i = scaleField k (spaceFieldE q hq n r ci dci b x) y i) ∧
  ((∀ y : Maxwell.Space, ‖y‖ < Rof q hq n r / k → ∀ i : Fin 3,
      scaleField k (physH q hq n r ci dci x) y i = scaleField k (spaceFieldH q hq n r ci dci b x) y i) ∧
    (∀ y : Maxwell.Space, Xof q hq n r / k < ‖y‖ → ∀ i : Fin 3,
      scaleField k (physH q hq n r ci dci x) y i = scaleField k (spaceFieldH q hq n r ci dci b x) y i) ∧
    ∀ i : Fin 3, (fun y => scaleField k (physH q hq n r ci dci x) y i) =ᵐ[volume]
      fun y => scaleField k (spaceFieldH q hq n r ci dci b x) y i)

/-- **The physical identification transports along the dilation.**  The identification of the physical fields with
the space versions of the piecewise fields implies the identification of the dilated physical fields with the dilated
space fields on the dilated region. -/
theorem physicallyIdentified_scale (k : ℝ) (hk : 0 < k) (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)
    (ci : StaticCoefficient.Coefficient) (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec)
    (hP : PhysicallyIdentified q hq n r ci dci b x) : PhysicallyIdentifiedAt k q hq n r ci dci b x := by
  obtain ⟨⟨hE1, hE2⟩, hH1, hH2, hH3⟩ := hP
  have hqm := Measure.quasiMeasurePreserving_smul (volume : Measure Maxwell.Space) hk.ne'
  have hnorm : ∀ y : Maxwell.Space, ‖k • y‖ = k * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  have hout : ∀ y : Maxwell.Space, Xof q hq n r / k < ‖y‖ → Xof q hq n r < ‖k • y‖ := by
    intro y hy
    rw [hnorm]
    rw [div_lt_iff₀ hk] at hy
    linarith [hy]
  have hin : ∀ y : Maxwell.Space, ‖y‖ < Rof q hq n r / k → ‖k • y‖ < Rof q hq n r := by
    intro y hy
    rw [hnorm]
    rw [lt_div_iff₀ hk] at hy
    linarith [hy]
  unfold PhysicallyIdentifiedAt
  refine ⟨⟨fun i => ?_, fun y hy i => ?_⟩, fun y hy i => ?_, fun y hy i => ?_, fun i => ?_⟩
  · have h1 := hE1 i
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_physRegion q hq n r dci)] at h1
    have h2 := hqm.ae h1
    rw [Filter.EventuallyEq,
      ae_restrict_iff' ((measurableSet_physRegion q hq n r dci).preimage (measurable_const_smul k))]
    filter_upwards [h2] with y hy hyS
    rw [scaleField_apply, scaleField_apply]
    exact congrArg (fun z : ℂ => (k : ℂ) * z) (hy hyS)
  · rw [scaleField_apply, scaleField_apply, hE2 (k • y) (hout y hy) i]
  · rw [scaleField_apply, scaleField_apply, hH1 (k • y) (hin y hy) i]
  · rw [scaleField_apply, scaleField_apply, hH2 (k • y) (hout y hy) i]
  · have h1 : ∀ᵐ y ∂(volume : Measure Maxwell.Space),
        physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i := hH3 i
    have h2 := hqm.ae h1
    filter_upwards [h2] with y hy
    rw [scaleField_apply, scaleField_apply]
    exact congrArg (fun z : ℂ => (k : ℂ) * z) hy

/-! ### Plane points and the dilated piecewise device fields -/

/-- The embedding of the plane into space commutes with the dilation. -/
theorem planePoint_smul (k : ℝ) (ξ : PlaneInverseCube.Plane) :
    MaxwellPlaneTail.planePoint (k • ξ) = k • MaxwellPlaneTail.planePoint ξ := by
  ext i
  fin_cases i <;> simp [MaxwellPlaneTail.planePoint]

/-- **The dilated piecewise device fields are plane values of the dilated space fields.**  For the concrete doubled
device, eventually in the gain index `n`, for every input `x` and eventually in the shell index `r`: the dilated
physical identification holds, the dilated physical fields solve the weak frequency-`k` dielectric Maxwell system with
the dilated coefficient, and at every plane point `ξ` off the dilated circle `‖ξ‖ = radius r / k` the dilated
piecewise device fields `scaleMap k deviceFieldsE`, `scaleMap k deviceFieldsH` equal the dilated space fields
`scaleField k spaceFieldE`, `scaleField k spaceFieldH` at `planePoint ξ`. -/
theorem device_fields_scaled (k : ℝ) (hk : 0 < k) {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ)
    (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vec, ∀ᶠ r : ℕ in atTop,
      PhysicallyIdentifiedAt k q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
          (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x ∧
        TestMaxwell k (dielectric (scaleCoeff k (OQ14.ChannelMaterialThroughput.pairedCoeff q hq.le n r
            (devCoeff r0 y ρ χ h hχ q n))))
          (scaleField k (physE q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
            (devData r0 y ρ χ h R hρ hχ hi q hq n) x))
          (scaleField k (physH q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
            (devData r0 y ρ χ h R hρ hχ hi q hq n) x)) ∧
        ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
          scaleMap k (OQ14.RestrictedTEActualPiecewise.deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq
              (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                (OQ14.RestrictedTEActualDevice.devRadE r0 y ρ χ h R hρ hχ hi hq)) n r) x ξ =
            scaleField k (spaceFieldE q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
              (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x) (MaxwellPlaneTail.planePoint ξ) ∧
          scaleMap k (OQ14.RestrictedTEActualPiecewise.deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq
              (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                (OQ14.RestrictedTEActualDevice.devRadH r0 y ρ χ h R hρ hχ hi hq)) n r) x ξ =
            scaleField k (spaceFieldH q hq.le n r (devCoeff r0 y ρ χ h hχ q n)
              (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x) (MaxwellPlaneTail.planePoint ξ) := by
  filter_upwards [OQ14.PhysicalDeviceFields.device_fields_physical r0 y ρ χ h R hρ hχ hρh hi q hq,
    device_testMaxwell_scaled k hk r0 y ρ χ h R hρ hχ hi q hq] with n h1 h2
  intro x
  filter_upwards [h1 x, h2 x] with r hr hM
  obtain ⟨hid, hpt⟩ := hr
  refine ⟨physicallyIdentified_scale k hk _ _ n r _ _ _ x hid, hM, fun ξ hξ => ?_⟩
  have hξ' : ‖k • ξ‖ ≠ RadialPhaseLimit.radius r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    intro he
    apply hξ
    rw [eq_div_iff hk.ne', mul_comm]
    exact he
  obtain ⟨e1, e2⟩ := hpt (k • ξ) hξ'
  constructor
  · rw [scaleMap_apply, e1, planePoint_smul]
    rfl
  · rw [scaleMap_apply, e2, planePoint_smul]
    rfl

end OQ14.FrequencyScalingDevice

#print axioms OQ14.FrequencyScalingDevice.combined_testMaxwell
#print axioms OQ14.FrequencyScalingDevice.device_testMaxwell
#print axioms OQ14.FrequencyScalingDevice.device_testMaxwell_scaled
#print axioms OQ14.FrequencyScalingDevice.physicallyIdentified_scale
#print axioms OQ14.FrequencyScalingDevice.planePoint_smul
#print axioms OQ14.FrequencyScalingDevice.device_fields_scaled
