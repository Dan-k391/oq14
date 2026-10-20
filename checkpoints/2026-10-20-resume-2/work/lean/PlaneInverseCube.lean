import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Genuine two-dimensional inverse-cube tail integration -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.PlaneInverseCube

open MeasureTheory Metric Set
open scoped Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Radius := Ioi (0 : ℝ)
abbrev Sphere := sphere (0 : Plane) 1
abbrev Punctured := ({(0 : Plane)}ᶜ : Set Plane)

def profile (T t : ℝ) : ℝ := (Ioi T).indicator (fun s => (s^3)⁻¹) t
def diskConstant : ℝ := 2*(volume : Measure Plane).real (ball 0 1)

theorem integrable_norm_of_radial (f : ℝ → ℝ)
    (hf : IntegrableOn (fun t => t*f t) (Ioi (0 : ℝ))) :
    Integrable (fun x : Plane => f ‖x‖) := by
  have hr : Integrable (fun r : Radius => f r) (Measure.volumeIoiPow 1) := by
    simp only [Measure.volumeIoiPow,ENNReal.ofReal]
    rw [integrable_withDensity_iff_integrable_smul
      (measurable_subtype_coe.pow_const 1).real_toNNReal]
    simp only [pow_one,NNReal.smul_def,Real.coe_toNNReal _ (le_of_lt (Subtype.prop _)),smul_eq_mul]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hf
  have hprod : Integrable (fun p : Sphere × Radius => f p.2)
      ((volume : Measure Plane).toSphere.prod (Measure.volumeIoiPow 1)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hr
  have hpres : MeasurePreserving (homeomorphUnitSphereProd Plane)
      ((volume : Measure Plane).comap ((↑) : Punctured → Plane))
      ((volume : Measure Plane).toSphere.prod (Measure.volumeIoiPow 1)) := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin,Nat.reduceSub] using
      (volume : Measure Plane).measurePreserving_homeomorphUnitSphereProd
  have hpunctured := (hpres.integrable_comp_emb
    (homeomorphUnitSphereProd Plane).measurableEmbedding).mpr hprod
  have hi : IntegrableOn (fun x : Plane => f ‖x‖) ({(0 : Plane)}ᶜ) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mpr
    simpa only [Function.comp_def,homeomorphUnitSphereProd_apply_snd_coe] using hpunctured
  simpa only [IntegrableOn,restrict_compl_singleton] using hi

theorem radial_profile (T : ℝ) (hT : 0 < T) :
    (fun t => t*profile T t) = (Ioi T).indicator (fun t : ℝ => (t^2)⁻¹) := by
  funext t
  by_cases ht : T < t
  · simp only [profile,Set.indicator,mem_Ioi,if_pos ht]
    have hn : t ≠ 0 := ne_of_gt (hT.trans ht)
    field_simp
    ring
  · simp [profile,Set.indicator,ht]

theorem inverse_square_rpow (t : ℝ) : t^(-2 : ℝ) = (t^2)⁻¹ := by
  simpa only [Int.cast_neg,Int.cast_ofNat,zpow_neg,zpow_ofNat,inv_pow] using
    Real.rpow_intCast t (-2)

theorem inverse_square_integrable (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => (t^2)⁻¹) (Ioi T) := by
  simpa only [inverse_square_rpow] using
    integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT

theorem inverse_square_integral (T : ℝ) (hT : 0 < T) :
    (∫ t : ℝ in Ioi T, (t^2)⁻¹) = T⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT
  simpa only [inverse_square_rpow,show (-2 : ℝ)+1 = -1 by norm_num,
    Real.rpow_neg_one,neg_div_neg_eq,div_one] using h

theorem radial_profile_integrable (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t => t*profile T t) (Ioi (0 : ℝ)) := by
  rw [radial_profile T hT]
  have hi : Integrable ((Ioi T).indicator (fun t : ℝ => (t^2)⁻¹)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (inverse_square_integrable T hT)
  exact hi.integrableOn

theorem inverse_cube_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun x : Plane => profile T ‖x‖) :=
  integrable_norm_of_radial (profile T) (radial_profile_integrable T hT)

theorem inverse_cube_integral (T : ℝ) (hT : 0 < T) :
    (∫ x : Plane, profile T ‖x‖) = diskConstant/T := by
  have h := integral_fun_norm_addHaar (μ := (volume : Measure Plane)) (profile T)
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hdim] at h
  simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,smul_eq_mul] at h
  have hrad : (∫ t : ℝ in Ioi (0 : ℝ), t*profile T t) = T⁻¹ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [radial_profile T hT,integral_indicator measurableSet_Ioi]
      exact inverse_square_integral T hT
    · intro t ht
      have hn : ¬ T < t := by simp only [mem_Ioi,not_lt] at ht; linarith
      simp [profile,Set.indicator,hn]
  rw [hrad] at h
  exact h.trans (by dsimp [diskConstant]; ring)

theorem tail_integrable {f : Plane → ℂ} (T C : ℝ) (hT : 0 < T)
    (hf : AEStronglyMeasurable f (volume.restrict {x : Plane | T < ‖x‖}))
    (hb : ∀ x : Plane, T < ‖x‖ → ‖f x‖ ≤ C/‖x‖^3) :
    IntegrableOn f {x : Plane | T < ‖x‖} := by
  have hi := (inverse_cube_integrable T hT).const_mul C
  apply hi.integrableOn.mono' hf
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet]
    with x hx
  change T < ‖x‖ at hx
  simpa [profile,Set.indicator,hx,div_eq_mul_inv] using hb x hx

theorem tail_integral_bound {f : Plane → ℂ} (T C : ℝ) (hT : 0 < T)
    (hf : AEStronglyMeasurable f (volume.restrict {x : Plane | T < ‖x‖}))
    (hb : ∀ x : Plane, T < ‖x‖ → ‖f x‖ ≤ C/‖x‖^3) :
    (∫ x : Plane in {x : Plane | T < ‖x‖}, ‖f x‖) ≤ C*diskConstant/T := by
  have hi := tail_integrable T C hT hf hb
  have heq : (∫ x : Plane in {x : Plane | T < ‖x‖}, C*profile T ‖x‖) =
      C*diskConstant/T := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [integral_const_mul,inverse_cube_integral T hT]
      ring
    · intro x hx
      simp only [mem_setOf_eq] at hx
      simp [profile,Set.indicator,hx]
  rw [← heq]
  apply integral_mono_ae hi.norm (((inverse_cube_integrable T hT).const_mul C).integrableOn)
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet]
    with x hx
  change T < ‖x‖ at hx
  simpa [profile,Set.indicator,hx,div_eq_mul_inv] using hb x hx

end OQ14.PlaneInverseCube

#print axioms OQ14.PlaneInverseCube.integrable_norm_of_radial
#print axioms OQ14.PlaneInverseCube.radial_profile
#print axioms OQ14.PlaneInverseCube.inverse_square_rpow
#print axioms OQ14.PlaneInverseCube.inverse_square_integrable
#print axioms OQ14.PlaneInverseCube.inverse_square_integral
#print axioms OQ14.PlaneInverseCube.radial_profile_integrable
#print axioms OQ14.PlaneInverseCube.inverse_cube_integrable
#print axioms OQ14.PlaneInverseCube.inverse_cube_integral
#print axioms OQ14.PlaneInverseCube.tail_integrable
#print axioms OQ14.PlaneInverseCube.tail_integral_bound
