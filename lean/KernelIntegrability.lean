import DyadicKernel
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space

/-! # Local integrability of the actual three-dimensional Green kernels -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.KernelIntegrability

open MeasureTheory Set Metric OQ14.Maxwell
open scoped NNReal ENNReal

theorem radial_integrable (f : ℝ → ℝ)
    (hf : IntegrableOn (fun r : ℝ => r^2 * f r) (Ioi 0)) :
    Integrable (fun x : Space => f ‖x‖) := by
  have hi : Integrable (fun r : Ioi (0 : ℝ) => f r)
      (Measure.volumeIoiPow 2) := by
    simp only [Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integrable_withDensity_iff_integrable_smul]
    · have hh := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hf
      convert hh using 1
      ext r
      simp [NNReal.smul_def, Real.coe_toNNReal, sq_nonneg]
    · exact (measurable_subtype_coe.pow_const _).real_toNNReal
  have hp : Integrable (fun p : sphere (0 : Space) 1 × Ioi (0 : ℝ) => f p.2)
      ((volume : Measure Space).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa using (integrable_const (1 : ℝ) (μ := (volume : Measure Space).toSphere)).mul_prod hi
  have hm := ((volume : Measure Space).measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
    (Homeomorph.measurableEmbedding _) (g := fun p => f p.2)
  have hh : Integrable (fun x : ({(0 : Space)}ᶜ : Set Space) => f ‖x.val‖)
      ((volume : Measure Space).comap (↑)) := by
    apply hm.mpr
    simpa using hp
  have hs := (integrableOn_iff_comap_subtypeVal (f := fun x : Space => f ‖x‖)
    (μ := (volume : Measure Space)) (measurableSet_singleton (0 : Space)).compl).mpr hh
  simpa only [IntegrableOn, restrict_compl_singleton] using hs

theorem inverse_norm_integrable_ball (R : ℝ) :
    IntegrableOn (fun x : Space => ‖x‖⁻¹) (closedBall 0 R) := by
  classical
  have hg : Integrable ((Icc 0 R).indicator (fun r : ℝ => r)) :=
    (continuous_id.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hf : IntegrableOn (fun r : ℝ => r^2 * (if r ≤ R then r⁻¹ else 0)) (Ioi 0) := by
    apply hg.integrableOn.congr_fun _ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    by_cases h : r ≤ R
    · simp only [Set.indicator_of_mem (show r ∈ Icc 0 R from ⟨hr.le, h⟩), if_pos h]
      field_simp [hr0]
      ring
    · simp [Set.indicator_of_not_mem (show r ∉ Icc 0 R from fun hh => h hh.2), h]
  have hi := radial_integrable (fun r => if r ≤ R then r⁻¹ else 0) hf
  apply (integrable_indicator_iff measurableSet_closedBall).mp
  change Integrable (fun x : Space => if x ∈ closedBall 0 R then ‖x‖⁻¹ else 0)
  simpa only [mem_closedBall, dist_zero_right] using hi

theorem inverse_norm_sq_integrable_ball (R : ℝ) :
    IntegrableOn (fun x : Space => (‖x‖⁻¹)^2) (closedBall 0 R) := by
  classical
  have hg : Integrable ((Icc 0 R).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hf : IntegrableOn (fun r : ℝ => r^2 * (if r ≤ R then (r⁻¹)^2 else 0)) (Ioi 0) := by
    apply hg.integrableOn.congr_fun _ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    by_cases h : r ≤ R
    · simp only [Set.indicator_of_mem (show r ∈ Icc 0 R from ⟨hr.le, h⟩), if_pos h]
      field_simp [hr0]
    · simp [Set.indicator_of_not_mem (show r ∉ Icc 0 R from fun hh => h hh.2), h]
  have hi := radial_integrable (fun r => if r ≤ R then (r⁻¹)^2 else 0) hf
  apply (integrable_indicator_iff measurableSet_closedBall).mp
  change Integrable (fun x : Space => if x ∈ closedBall 0 R then (‖x‖⁻¹)^2 else 0)
  simpa only [mem_closedBall, dist_zero_right] using hi

theorem phi_measurable (k : ℝ) : Measurable (OQ14.GreenKernel.phi k) := by
  unfold OQ14.GreenKernel.phi OQ14.GreenKernel.radial
  fun_prop

theorem phi_norm (k : ℝ) (x : Space) :
    ‖OQ14.GreenKernel.phi k x‖ = (4 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
  rw [OQ14.GreenKernel.phi, norm_div, OQ14.GreenKernel.radial_norm]
  simp [norm_mul, abs_of_pos Real.pi_pos, div_eq_mul_inv, mul_comm]

theorem phi_integrable_ball (k R : ℝ) :
    IntegrableOn (OQ14.GreenKernel.phi k) (closedBall 0 R) := by
  apply ((inverse_norm_integrable_ball R).const_mul ((4 * Real.pi)⁻¹)).mono'
    (phi_measurable k).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => (phi_norm k x).le)

theorem phi_memLp_two_ball (k R : ℝ) :
    MemLp (OQ14.GreenKernel.phi k) 2 (volume.restrict (closedBall 0 R)) := by
  apply (memLp_two_iff_integrable_sq_norm (phi_measurable k).aestronglyMeasurable).mpr
  simpa only [phi_norm, mul_pow] using
    (inverse_norm_sq_integrable_ball R).const_mul (((4 * Real.pi)⁻¹)^2)

theorem inverse_norm_locallyIntegrable :
    LocallyIntegrable (fun x : Space => ‖x‖⁻¹) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (inverse_norm_integrable_ball R).mono_set hR

theorem inverse_norm_sq_locallyIntegrable :
    LocallyIntegrable (fun x : Space => (‖x‖⁻¹)^2) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (inverse_norm_sq_integrable_ball R).mono_set hR

theorem phi_locallyIntegrable (k : ℝ) : LocallyIntegrable (OQ14.GreenKernel.phi k) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (phi_integrable_ball k R).mono_set hR

end OQ14.KernelIntegrability

#print axioms OQ14.KernelIntegrability.radial_integrable
#print axioms OQ14.KernelIntegrability.inverse_norm_integrable_ball
#print axioms OQ14.KernelIntegrability.inverse_norm_sq_integrable_ball
#print axioms OQ14.KernelIntegrability.phi_measurable
#print axioms OQ14.KernelIntegrability.phi_norm
#print axioms OQ14.KernelIntegrability.phi_integrable_ball
#print axioms OQ14.KernelIntegrability.phi_memLp_two_ball
#print axioms OQ14.KernelIntegrability.inverse_norm_locallyIntegrable
#print axioms OQ14.KernelIntegrability.inverse_norm_sq_locallyIntegrable
#print axioms OQ14.KernelIntegrability.phi_locallyIntegrable
