import CountedSubspacesVolume
import PhysicalPlaneFlux

/-! Whole-plane flux integrability of the same finite physical device. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.PhysicalDeviceFlux
open MeasureTheory Filter Topology Metric Set
open RestrictedTEActualCore RestrictedTEActualFields RestrictedTEActualPiecewise
  RestrictedTEActualCounting RestrictedTEPartnerSmallness RestrictedTEDipoleProfile
  RestrictedTEConcreteDevice RestrictedTEActualPhase RestrictedTEActualDevice

abbrev FieldMap := RestrictedTEActualFields.FieldMap
abbrev Vec := RestrictedTEActualCore.Vec

section Device
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
  (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
  (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
  (hρh : ρ < h) (q : ℝ) (hq : 1 < q)

def electric : ℕ → ℕ → FieldMap :=
  deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
    (RestrictedTEBackgroundOutside.outFieldE q hq.le (devRadE r0 y ρ χ h R hρ hχ hi hq))

def magnetic : ℕ → ℕ → FieldMap :=
  deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
    (RestrictedTEBackgroundOutside.outFieldH q hq.le (devRadH r0 y ρ χ h R hρ hχ hi hq))

theorem core_agreement :
    CoreAgreement r0 y ρ χ h R hρ hχ hi q hq
      (electric r0 y ρ χ h R hρ hχ hi hρh q hq)
      (magnetic r0 y ρ χ h R hρ hχ hi hρh q hq) := by
  let outE := RestrictedTEBackgroundOutside.outFieldE q hq.le (devRadE r0 y ρ χ h R hρ hχ hi hq)
  let outH := RestrictedTEBackgroundOutside.outFieldH q hq.le (devRadH r0 y ρ χ h R hρ hχ hi hq)
  let radE := devRadE r0 y ρ χ h R hρ hχ hi hq
  let radH := devRadH r0 y ρ χ h R hρ hχ hi hq
  have hOD := RestrictedTEBackgroundOutside.outsideDecomposition_of_radiated q hq.le radE radH
    (devRad_hrad r0 y ρ χ h R hρ hχ hi hq)
  have hCM := CoreMajorantDevice.coreMajorant_device r0 y ρ χ h R hρ hχ hρh hi q hq
  have hd := concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
  refine coreAgreement_of_out r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE outH ?_ ?_
  · intro n r x i
    exact ⟨(RestrictedTEBackgroundOutside.bgOutE_meas q hq.le n r x i).add
      (devRad_meas r0 y ρ χ h R hρ hχ hi hq n r x i).1,
      (RestrictedTEBackgroundOutside.bgOutH_meas q hq.le n r x i).add
      (devRad_meas r0 y ρ χ h R hρ hχ hi hq n r x i).2⟩
  ·
    filter_upwards [hCM.maj, hOD.rad] with n hn1 hn2
    intro N' B horth
    obtain ⟨C1, ρ1, r1, hc⟩ := hn1 N' B horth
    obtain ⟨K1, K2, L1, L2, r2, hrad⟩ := hn2 N' B horth
    obtain ⟨C2, r2', hT2⟩ := outside_majorant_of_pieces q hq.le outE outH
      (fun n r x ξ => radE n r x ξ) (fun n r x ξ => radH n r x ξ) hOD n N' B horth
      ⟨K1, K2, L1, L2, r2, hrad⟩
    obtain ⟨rb, hrb⟩ := Filter.eventually_atTop.mp
      (SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1))
    have hT1 : ∃ (C1' ρ1' : ℝ) (r1' : ℕ), ∀ r ≥ r1',
        ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
        ∀ ξ : PlaneInverseCube.Plane, ρ1' ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
          ‖OQ14.RestrictedTEActualFields.fieldFlux
            (OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
            (OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) x ξ‖ ≤ C1' / ‖ξ‖ ^ 3 := by
      refine ⟨C1, ρ1, max r1 rb, fun r hr x hx ξ hξ hlt => ?_⟩
      have hbr := hrb r ((le_max_right _ _).trans hr)
      unfold OQ14.RestrictedTEActualFields.fieldFlux
      rw [OQ14.RestrictedTEActualCore.deviceFieldE_apply hd hq (le_max_left R 1) n r hbr x ξ hlt,
        OQ14.RestrictedTEActualCore.deviceFieldH_apply hd hq (le_max_left R 1) n r hbr x ξ hlt]
      exact hc r ((le_max_left _ _).trans hr) x hx.1 hx.2 ξ hξ hlt
    have hT2' : ∃ (C2' : ℝ) (r2'' : ℕ), ∀ r ≥ r2'',
        ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
        ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
          ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2' / ‖ξ‖ ^ 3 :=
      ⟨C2, r2', fun r hr x hx ξ hξ => hT2 r hr x hx.1 hx.2 ξ hξ⟩
    obtain ⟨C, ρ1', r1', ht⟩ := tail_of_two_majorants (fun r => RadialPhaseLimit.radius r)
      (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
      (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) outE outH n
      {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1} hT1 hT2'
    exact ⟨C, ρ1', r1', fun r hr x hx hp ξ hξ => ht r hr x ⟨hx, hp⟩ ξ hξ⟩

theorem unit_integrable_eventually (hR : 0 ≤ R) (N : ℕ) (A : Fin N → Vec)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      RestrictedTEIncoming.physicalPower x = 1 →
        Integrable (fieldFlux (electric r0 y ρ χ h R hρ hχ hi hρh q hq n r)
          (magnetic r0 y ρ χ h R hρ hχ hi hρh q hq n r) x) volume := by
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have he := ActualFieldEstimatesPhase.of_core r0 y ρ χ h R hρ hχ hi hρh hq hb0
    (le_max_left R 1) (BackgroundTransmissionParity.parityPhase q)
    (Eventually.of_forall (BackgroundTransmissionParity.parityPhase_norm q))
    (Eventually.of_forall (fun n x => BackgroundTransmissionParity.input_scaledCoeff q hq.le n x))
    _ _ (core_agreement r0 y ρ χ h R hρ hχ hi hρh q hq)
  obtain ⟨n0, hn0, hest⟩ := ActualFieldEstimatesPhase.rephase r0 y ρ χ h R hρ hχ hi hR hρh q hq _ _ _ he
  have hI := L1Interface_of_field_estimates r0 y ρ χ h R hρ hχ hi hR hρh q hq _ _ hest
  filter_upwards [eventually_ge_atTop n0] with n hn
  filter_upwards [hI N A horth n 1 one_pos] with r hr x hx hp
  have hh := (hr x hx hp).1
  rw [rephaseFields_ge n0 (BackgroundTransmissionParity.parityPhase q) _ _ n r hn,
    rephaseFields_ge n0 (BackgroundTransmissionParity.parityPhase q) _ _ n r hn,
    fieldFlux_rephase _ (hn0 n hn)] at hh
  exact hh

theorem integrable_of_unit (E H : FieldMap) (N : ℕ) (A : Fin N → Vec)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)))
    (hunit : ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
      Integrable (fieldFlux E H x) volume) :
    ∀ x ∈ Submodule.span ℂ (Set.range A), Integrable (fieldFlux E H x) volume := by
  intro x hx
  by_cases hp : RestrictedTEIncoming.physicalPower x = 0
  · have hx0 := span_power_zero A horth x hx hp
    have hf0 : fieldFlux E H 0 = (fun _ => 0) := by
      funext ξ
      simp [fieldFlux_eq]
    rw [hx0, hf0]
    exact integrable_zero _ _ _
  · have hP : 0 < RestrictedTEIncoming.physicalPower x :=
      lt_of_le_of_ne (RestrictedTEIncoming.physical_power_nonnegative x) (Ne.symm hp)
    let z : ℂ := ((Real.sqrt (RestrictedTEIncoming.physicalPower x))⁻¹ : ℝ)
    have hz : ‖z‖ ^ 2 = (RestrictedTEIncoming.physicalPower x)⁻¹ := by
      simp only [z, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      rw [inv_pow, Real.sq_sqrt hP.le]
    have hp1 : RestrictedTEIncoming.physicalPower (z • x) = 1 := by
      rw [RestrictedTEHomogeneousCount.physicalPower_smul, hz, inv_mul_cancel₀ hP.ne']
    have hi := hunit (z • x) ((Submodule.span ℂ (Set.range A)).smul_mem z hx) hp1
    have hf := fieldFlux_homogeneous (fun _ _ => E) (fun _ _ => H) 0 0 z x
    change fieldFlux E H (z • x) = (fun ξ => ((‖z‖ ^ 2 : ℝ) : ℂ) * fieldFlux E H x ξ) at hf
    rw [hf, hz] at hi
    have hc : (((RestrictedTEIncoming.physicalPower x)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero hP.ne'
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hi

theorem integrable_eventually (hR : 0 ≤ R) (N : ℕ) (A : Fin N → Vec)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      Integrable (fieldFlux (electric r0 y ρ χ h R hρ hχ hi hρh q hq n r)
        (magnetic r0 y ρ χ h R hρ hχ hi hρh q hq n r) x) volume := by
  filter_upwards [unit_integrable_eventually r0 y ρ χ h R hρ hχ hi hρh q hq hR N A horth] with n hn
  filter_upwards [hn] with r hr
  exact integrable_of_unit _ _ N A horth hr

theorem scaled_integrable_eventually (k : ℝ) (hk : 0 < k) (hR : 0 ≤ R) (N : ℕ) (A : Fin N → Vec)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      Integrable (fieldFlux (FrequencyScalingFlux.scaleMap k (electric r0 y ρ χ h R hρ hχ hi hρh q hq n r))
        (FrequencyScalingFlux.scaleMap k (magnetic r0 y ρ χ h R hρ hχ hi hρh q hq n r)) x) volume := by
  filter_upwards [integrable_eventually r0 y ρ χ h R hρ hχ hi hρh q hq hR N A horth] with n hn
  filter_upwards [hn] with r hr x hx
  rw [FrequencyScalingFlux.fieldFlux_scale_fun]
  exact ((hr x hx).comp_smul hk.ne').const_mul _

end Device
end OQ14.PhysicalDeviceFlux

#print axioms OQ14.PhysicalDeviceFlux.core_agreement
#print axioms OQ14.PhysicalDeviceFlux.unit_integrable_eventually
#print axioms OQ14.PhysicalDeviceFlux.integrable_of_unit
#print axioms OQ14.PhysicalDeviceFlux.integrable_eventually
#print axioms OQ14.PhysicalDeviceFlux.scaled_integrable_eventually
