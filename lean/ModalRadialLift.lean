import ModalVolumeAngularCoefficients
import ComplexPolarIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OQ14.ModalRadialLift
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarIntegration
open scoped Topology

theorem radial_memLp (g : ℝ → ℂ) (hg : StronglyMeasurable g)
    (hweighted : MemLp (fun r : ℝ => (r : ℂ)*g r) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (fun x : Space => g ‖x‖) 2 volume := by
  have hi : IntegrableOn (fun r : ℝ => ‖(r : ℂ)*g r‖^2) (Ioi (0 : ℝ)) :=
    hweighted.norm.integrable_sq
  have hr : Integrable (fun r : Radius => ‖g r‖^2) radialMeasure := by
    apply (ComplexPolarIntegration.integrable_radialMeasure_iff _).mpr
    have hi' : IntegrableOn (fun r : ℝ => r^2 * ‖g r‖^2) (Ioi (0 : ℝ)) := by
      apply hi.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < r from hr), mul_pow]
    simpa only [Function.comp_def, smul_eq_mul] using
      (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi'
  have hs : Integrable (fun p : Sphere × Radius => ‖g (p.2 : ℝ)‖^2) (angularMeasure.prod radialMeasure) := by
    have hconst : Integrable (fun _ : Sphere => (1 : ℝ)) angularMeasure := integrable_const 1
    have h := hconst.mul_prod hr
    simpa using h
  have hp := (polar_measurePreserving.integrable_comp_emb
    (homeomorphUnitSphereProd Space).measurableEmbedding
    (g := fun p : Sphere × Radius => ‖g (p.2 : ℝ)‖^2)).mpr hs
  have hx : IntegrableOn (fun x : Space => ‖g ‖x‖‖^2) ({0}ᶜ : Set Space) := by
    apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mpr
    simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using hp
  have hall : Integrable (fun x : Space => ‖g ‖x‖‖^2) volume := by
    change Integrable (fun x : Space => ‖g ‖x‖‖^2) (volume.restrict ({0}ᶜ : Set Space)) at hx
    rwa [restrict_compl_singleton] at hx
  exact (memLp_two_iff_integrable_sq_norm (hg.comp_measurable continuous_norm.measurable).aestronglyMeasurable).mpr hall

#print axioms OQ14.ModalRadialLift.radial_memLp
end OQ14.ModalRadialLift



