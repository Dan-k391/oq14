import Packet04VectorAngular
import ComplexPolarIntegration

/-! Actual vector L² fields are recovered from countably many sphere moments.
The exceptional radii are combined only over a countable harmonic basis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04SliceRecovery
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalVectorAngularSlices OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

theorem eq_of_slices (u v : VectorFourier.VectorL2)
    (h : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), slice u r = slice v r) :
    u = v := by
  let f := physical u - physical v
  have hi : Integrable (fun x : Space => ‖f x‖^2) := (Lp.memLp f).norm.integrable_sq
  have hr : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      (∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) = 0 := by
    filter_upwards [h, slice_actual_ae u, slice_actual_ae v,
      PolarMomentAE.polar_ae (physical_ae u), PolarMomentAE.polar_ae (physical_ae v),
      PolarMomentAE.polar_ae (Lp.coeFn_sub (physical u) (physical v))] with r he hu hv hpu hpv hf
    apply integral_eq_zero_of_ae
    filter_upwards [hu, hv, hpu, hpv, hf] with ω hu hv hpu hpv hf
    change (physical u - physical v) (r • (ω : Space)) = _ at hf
    have huv : u (VectorFourier.coordinateMap (r • (ω : Space))) =
        v (VectorFourier.coordinateMap (r • (ω : Space))) := hu.symm.trans (he ▸ hv)
    change ‖(physical u - physical v) (r • (ω : Space))‖^2 = 0
    rw [hf]
    change ‖physical u (r • (ω : Space)) - physical v (r • (ω : Space))‖^2 = 0
    rw [hpu, hpv, huv, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hz : (∫ x : Space, ‖f x‖^2) = 0 := by
    rw [ComplexPolarIntegration.integral_polar _ hi]
    apply integral_eq_zero_of_ae
    filter_upwards [hr] with r hr
    simp only [hr, smul_zero, Pi.zero_apply]
  have hzero : f = 0 := by
    apply Lp.ext
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hz,
      Lp.coeFn_zero ComplexVectorSphere.Vector 2 (volume : Measure Space)] with x hx h0
    rw [h0]
    exact norm_eq_zero.mp (pow_eq_zero hx)
  have he : physical u = physical v := sub_eq_zero.mp hzero
  exact (Lp.compMeasurePreservingₗᵢ ℂ VectorFourier.coordinateMap
    VectorFourier.coordinateMap_preserving).injective he

def modeMoment (u : VectorFourier.VectorL2)
    (m : C(Sphere, Space)) (r : ℝ) : ℂ :=
  ∫ ω : Sphere, ⟪embedVector (m ω),
    u (VectorFourier.coordinateMap (r • (ω : Space)))⟫ ∂angularMeasure

theorem modeMoment_actual (u : VectorFourier.VectorL2) (m : C(Sphere, Space)) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), modeMoment u m r =
      ∫ ω : Sphere, ⟪embedVector (m ω), slice u r ω⟫ ∂angularMeasure := by
  filter_upwards [slice_actual_ae u] with r hr
  apply integral_congr_ae
  filter_upwards [hr] with ω hω
  rw [hω]

def supportedInUnit (u : VectorFourier.VectorL2) : Prop :=
  ∀ᵐ x : Space ∂volume, 1 ≤ ‖x‖ → u (VectorFourier.coordinateMap x) = 0

theorem supportedInUnit_smul (c : ℂ) (u : VectorFourier.VectorL2)
    (hu : supportedInUnit u) : supportedInUnit (c • u) := by
  have hc := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c u)
  filter_upwards [hu, hc] with x hu hc hx
  rw [hc]
  change c • u (VectorFourier.coordinateMap x) = 0
  rw [hu hx, smul_zero]

theorem slice_smul (c : ℂ) (u : VectorFourier.VectorL2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), slice (c • u) r = c • slice u r := by
  have hc := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c u)
  filter_upwards [slice_actual_ae (c • u), slice_actual_ae u,
    PolarMomentAE.polar_ae hc] with r hcu hu hc
  apply Lp.ext
  filter_upwards [hcu, hu, hc, Lp.coeFn_smul c (slice u r)] with ω hcu hu hc hs
  rw [hcu, hc, hs]
  change c • u (VectorFourier.coordinateMap (r • (ω : Space))) = c • slice u r ω
  rw [hu]

theorem slices_zero_outside (u : VectorFourier.VectorL2) (hu : supportedInUnit u) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), 1 ≤ r → slice u r = 0 := by
  filter_upwards [PolarMomentAE.polar_ae hu, slice_actual_ae u,
    ae_restrict_mem measurableSet_Ioi] with r hu hs hr hlarge
  apply Lp.ext
  filter_upwards [hu, hs, Lp.coeFn_zero ComplexVectorSphere.Vector 2 angularMeasure] with ω hu hs h0
  rw [hs, h0]
  apply hu
  simpa [norm_smul, sphere_norm, abs_of_pos (show 0 < r from hr)] using hlarge

theorem eq_of_slices_inside (u v : VectorFourier.VectorL2)
    (hu : supportedInUnit u) (hv : supportedInUnit v)
    (h : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), slice u r = slice v r) :
    u = v := by
  apply eq_of_slices
  filter_upwards [slices_zero_outside u hu, slices_zero_outside v hv,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp h),
    ae_restrict_mem measurableSet_Ioi] with r hu hv hi hr
  by_cases hsmall : r < 1
  · exact hi ⟨hr, hsmall⟩
  · exact (hu (le_of_not_gt hsmall)).trans (hv (le_of_not_gt hsmall)).symm

theorem eq_of_mode_moments (u v : VectorFourier.VectorL2)
    (hR : ∀ a, ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      modeMoment u (VectorHarmonicBasisSpan.radialField a) r =
        modeMoment v (VectorHarmonicBasisSpan.radialField a) r)
    (hP : ∀ a, ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      modeMoment u (VectorHarmonicBasisSpan.poloidalField a) r =
        modeMoment v (VectorHarmonicBasisSpan.poloidalField a) r)
    (hT : ∀ a, ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      modeMoment u (VectorHarmonicBasisSpan.toroidalField a) r =
        modeMoment v (VectorHarmonicBasisSpan.toroidalField a) r) : u = v := by
  apply eq_of_slices
  have hmode (m : C(Sphere, Space)) :
      ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      modeMoment u m r = modeMoment v m r →
      (∫ ω : Sphere, ⟪embedVector (m ω), slice u r ω⟫ ∂angularMeasure) =
        ∫ ω : Sphere, ⟪embedVector (m ω), slice v r ω⟫ ∂angularMeasure := by
    filter_upwards [modeMoment_actual u m, modeMoment_actual v m] with r hu hv he
    exact hu.symm.trans (he.trans hv)
  have hR' := ae_all_iff.mpr (fun a => (hR a).and (hmode (VectorHarmonicBasisSpan.radialField a)))
  have hP' := ae_all_iff.mpr (fun a => (hP a).and (hmode (VectorHarmonicBasisSpan.poloidalField a)))
  have hT' := ae_all_iff.mpr (fun a => (hT a).and (hmode (VectorHarmonicBasisSpan.toroidalField a)))
  filter_upwards [hR', hP', hT'] with r hr hp ht
  exact Packet04VectorAngular.eq_of_polynomial_integral_moments _ _
    (fun a => (hr a).2 (hr a).1) (fun a => (hp a).2 (hp a).1)
    (fun a => (ht a).2 (ht a).1)

end OQ14.Packet04SliceRecovery
#print axioms OQ14.Packet04SliceRecovery.eq_of_slices
#print axioms OQ14.Packet04SliceRecovery.modeMoment_actual
#print axioms OQ14.Packet04SliceRecovery.supportedInUnit_smul
#print axioms OQ14.Packet04SliceRecovery.slice_smul
#print axioms OQ14.Packet04SliceRecovery.slices_zero_outside
#print axioms OQ14.Packet04SliceRecovery.eq_of_slices_inside
#print axioms OQ14.Packet04SliceRecovery.eq_of_mode_moments
