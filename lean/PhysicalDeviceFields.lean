import PhysicalFieldIdentification
import RestrictedTEActualDevice

/-! The exact fields of the final counting theorem are the physical fields.

`RestrictedTEActualDevice.actual_counted_subspaces_device` counts the plane flux of the piecewise device fields
`deviceFieldsE`, `deviceFieldsH` with the outside fields `outFieldE`, `outFieldH` built from the radiated plane fields
`devRadE`, `devRadH`.  Those are the radiated series only when `radThreshold q hq n b ≤ r` and
`radius r < ‖ξ‖`, and are zero otherwise.  This module shows that, for every gain index `n` beyond the unit threshold,
every input `x` and every shell index `r` beyond the thresholds, these exact fields agree with the space versions
`spaceFieldE`, `spaceFieldH` of the physical fields (`PhysicalFieldIdentification.PhysicallyIdentified`) at every plane
point off the circle `‖ξ‖ = radius r` (and hence for almost every plane point, the circle being null). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.PhysicalDeviceFields
open MeasureTheory Filter Topology

/-- Beyond the threshold and outside the circle, the radiated electric plane field of the device module is the
radiated series `radiatedE` at the plane point. -/
theorem radElec_eq_radiatedE (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (r : ℕ) (x : OQ14.RestrictedTEActualCore.Vec)
    (ξ : PlaneInverseCube.Plane)
    (hc : OQ14.RestrictedTEActualDevice.radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖) :
    OQ14.RestrictedTEActualDevice.radElec q hq n ci dci b r x ξ =
      OQ14.PhysicalFieldIdentification.radiatedE q hq n r ci dci b x (MaxwellPlaneTail.planePoint ξ) := by
  unfold OQ14.RestrictedTEActualDevice.radElec OQ14.PhysicalFieldIdentification.radiatedE
  rw [if_pos hc]
  unfold OQ14.SourceRadiatedFlux.genElectric
  rw [OQ14.PhysicalFieldIdentification.coeffFam_congr
    (fun _ j => DynamicVolume.source ci (OQ14.RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) j)
    (OQ14.PhysicalFieldIdentification.radCoeff q hq n ci dci b x) r rfl]

/-- The magnetic analogue. -/
theorem radMag_eq_radiatedH (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (r : ℕ) (x : OQ14.RestrictedTEActualCore.Vec)
    (ξ : PlaneInverseCube.Plane)
    (hc : OQ14.RestrictedTEActualDevice.radThreshold q hq n b ≤ r ∧ RadialPhaseLimit.radius r < ‖ξ‖) :
    OQ14.RestrictedTEActualDevice.radMag q hq n ci dci b r x ξ =
      OQ14.PhysicalFieldIdentification.radiatedH q hq n r ci dci b x (MaxwellPlaneTail.planePoint ξ) := by
  unfold OQ14.RestrictedTEActualDevice.radMag OQ14.PhysicalFieldIdentification.radiatedH
  rw [if_pos hc]
  unfold OQ14.SourceRadiatedFlux.genMagnetic
  rw [OQ14.PhysicalFieldIdentification.coeffFam_congr
    (fun _ j => DynamicVolume.source ci (OQ14.RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) j)
    (OQ14.PhysicalFieldIdentification.radCoeff q hq n ci dci b x) r rfl]

/-- **The exact fields of the final counting theorem are the physical fields.**  For the concrete doubled device,
eventually in the gain index `n`, for every input `x` and eventually in the shell index `r`: the physical fields are
identified with the space versions of the piecewise fields, and at every plane point `ξ` off the circle
`‖ξ‖ = radius r`, the piecewise device fields `deviceFieldsE`, `deviceFieldsH` (with the outside fields built from
`devRadE`, `devRadH`) equal the space versions `spaceFieldE`, `spaceFieldH` at `planePoint ξ`. -/
theorem device_fields_physical {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : OQ14.RestrictedTEActualCore.Vec, ∀ᶠ r : ℕ in atTop,
      OQ14.PhysicalFieldIdentification.PhysicallyIdentified q hq.le n r
        (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
        (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x ∧
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r →
        OQ14.RestrictedTEActualPiecewise.deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (OQ14.RestrictedTEActualDevice.devRadE r0 y ρ χ h R hρ hχ hi hq)) n r x ξ =
          OQ14.PhysicalFieldIdentification.spaceFieldE q hq.le n r
            (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
            (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ) ∧
        OQ14.RestrictedTEActualPiecewise.deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (OQ14.RestrictedTEActualDevice.devRadH r0 y ρ χ h R hρ hχ hi hq)) n r x ξ =
          OQ14.PhysicalFieldIdentification.spaceFieldH q hq.le n r
            (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
            (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ) := by
  filter_upwards [OQ14.PhysicalFieldIdentification.device_physical_identification r0 y ρ χ h R hρ hχ hi q hq]
    with n hn
  intro x
  filter_upwards [hn x, SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1),
    Filter.eventually_ge_atTop (OQ14.RestrictedTEActualDevice.radThreshold q hq.le n (max R 1))]
    with r h1 hbr hth
  refine ⟨h1, fun ξ hξ => ?_⟩
  have hd := OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
  rcases lt_or_gt_of_ne hξ with hlt | hgt
  · have hpn : ‖MaxwellPlaneTail.planePoint ξ‖ < OQ14.PhysicalFieldIdentification.Rof q hq.le n r := by
      rw [MaxwellPlaneTail.planePoint_norm]
      exact hlt
    constructor
    · unfold OQ14.RestrictedTEActualPiecewise.deviceFieldsE
      funext i
      rw [OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ hlt,
        OQ14.RestrictedTEActualCore.deviceFieldE_apply hd hq (le_max_left R 1) n r hbr x ξ hlt,
        OQ14.PhysicalFieldIdentification.spaceFieldE_core q hq.le n r _ _ (max R 1) x _ i hpn]
      rfl
    · unfold OQ14.RestrictedTEActualPiecewise.deviceFieldsH
      funext i
      rw [OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ hlt,
        OQ14.RestrictedTEActualCore.deviceFieldH_apply hd hq (le_max_left R 1) n r hbr x ξ hlt,
        OQ14.PhysicalFieldIdentification.spaceFieldH_core q hq.le n r _ _ (max R 1) x _ i hpn]
      rfl
  · have hpn : OQ14.PhysicalFieldIdentification.Rof q hq.le n r ≤ ‖MaxwellPlaneTail.planePoint ξ‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]
      exact hgt.le
    have hcond : OQ14.RestrictedTEActualDevice.radThreshold q hq.le n (max R 1) ≤ r ∧
        RadialPhaseLimit.radius r < ‖ξ‖ := ⟨hth, hgt⟩
    constructor
    · unfold OQ14.RestrictedTEActualPiecewise.deviceFieldsE
      funext i
      rw [OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_ge (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ
          hgt.le,
        OQ14.PhysicalFieldIdentification.spaceFieldE_out q hq.le n r _ _ (max R 1) x _ i hpn]
      have e : OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
            (OQ14.RestrictedTEActualDevice.devRadE r0 y ρ χ h R hρ hχ hi hq) n r x ξ i =
          OQ14.RestrictedTEActualPiecewise.bgFieldE q hq.le n r x (MaxwellPlaneTail.planePoint ξ) i +
            OQ14.RestrictedTEActualDevice.radElec q hq.le n _ _ (max R 1) r x ξ i := rfl
      rw [e, radElec_eq_radiatedE q hq.le n _ _ (max R 1) r x ξ hcond]
    · unfold OQ14.RestrictedTEActualPiecewise.deviceFieldsH
      funext i
      rw [OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_ge (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ
          hgt.le,
        OQ14.PhysicalFieldIdentification.spaceFieldH_out q hq.le n r _ _ (max R 1) x _ i hpn]
      have e : OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
            (OQ14.RestrictedTEActualDevice.devRadH r0 y ρ χ h R hρ hχ hi hq) n r x ξ i =
          OQ14.RestrictedTEActualPiecewise.bgFieldH q hq.le n r x (MaxwellPlaneTail.planePoint ξ) i +
            OQ14.RestrictedTEActualDevice.radMag q hq.le n _ _ (max R 1) r x ξ i := rfl
      rw [e, radMag_eq_radiatedH q hq.le n _ _ (max R 1) r x ξ hcond]

/-- The same equalities hold for almost every plane point (the circle `‖ξ‖ = radius r` is null). -/
theorem device_fields_physical_ae {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : OQ14.RestrictedTEActualCore.Vec, ∀ᶠ r : ℕ in atTop,
      OQ14.PhysicalFieldIdentification.PhysicallyIdentified q hq.le n r
        (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
        (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x ∧
      ∀ᵐ ξ ∂(volume : Measure PlaneInverseCube.Plane),
        OQ14.RestrictedTEActualPiecewise.deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (OQ14.RestrictedTEActualDevice.devRadE r0 y ρ χ h R hρ hχ hi hq)) n r x ξ =
          OQ14.PhysicalFieldIdentification.spaceFieldE q hq.le n r
            (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
            (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ) ∧
        OQ14.RestrictedTEActualPiecewise.deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (OQ14.RestrictedTEActualDevice.devRadH r0 y ρ χ h R hρ hχ hi hq)) n r x ξ =
          OQ14.PhysicalFieldIdentification.spaceFieldH q hq.le n r
            (OQ14.PhysicalFieldIdentification.devCoeff r0 y ρ χ h hχ q n)
            (OQ14.PhysicalFieldIdentification.devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ) := by
  filter_upwards [device_fields_physical r0 y ρ χ h R hρ hχ hρh hi q hq] with n hn
  intro x
  filter_upwards [hn x] with r hr
  refine ⟨hr.1, ?_⟩
  have hnull : ∀ᵐ ξ ∂(volume : Measure PlaneInverseCube.Plane), ‖ξ‖ ≠ RadialPhaseLimit.radius r := by
    apply ae_iff.mpr
    simpa using OQ14.SourceRadiatedAnnulus.sphere_null (RadialPhaseLimit.radius r)
  filter_upwards [hnull] with ξ hξ
  exact hr.2 ξ hξ

end OQ14.PhysicalDeviceFields

#print axioms OQ14.PhysicalDeviceFields.radElec_eq_radiatedE
#print axioms OQ14.PhysicalDeviceFields.radMag_eq_radiatedH
#print axioms OQ14.PhysicalDeviceFields.device_fields_physical
#print axioms OQ14.PhysicalDeviceFields.device_fields_physical_ae
