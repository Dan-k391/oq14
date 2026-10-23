import RestrictedTECoherentTail
import RestrictedTEScale
import StaticTrialLimit

/-! Actual harmonic TE trial free flux converges to its static coherent field on the whole plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTETrialLimit
open Complex MeasureTheory Metric Set Filter Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate

theorem error_smul (S : Source) (c : ℂ) (A : Index →₀ ℂ) (q : Plane) :
    coherentError S (c • A) q=conj c*coherentError S A q := by
  simp [coherentError,dynamicMixed,staticMixed,RestrictedTEScale.magnetic_smul,cross_apply,conjugate]
  ring

theorem trial_identity (S : Source) (c : ℂ) (A : Index →₀ ℂ) (q : Plane) :
    freeFlux S (c • A) q-staticMixed S (c • A) q=
      conj c*coherentError S A q+MaxwellPlaneL1.flux 1 S S q := by
  rw [free_identity,← error_smul]
  unfold coherentError
  ring

theorem trial_to_static (A : Index →₀ ℂ) (R γ M : ℝ) (hR : 0≤R) (hγ : 0<γ) (hM : 0≤M)
    (S : ℝ → Source)
    (hS : ∀ᶠ a : ℝ in 𝓝[>] 0, Admissible R (γ*a) (S a))
    (hm : ∀ᶠ a : ℝ in 𝓝[>] 0, sourceMass (S a)≤M*a^2) :
    Tendsto (fun a : ℝ => ∫ q : Plane, ‖freeFlux (S a) ((a : ℂ)⁻¹ • A) q-
      staticMixed (S a) ((a : ℂ)⁻¹ • A) q‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨W,hW,T,hT,hTR,hwhole⟩ := RestrictedTECoherentTail.whole_error_mass A R hR
  have h1 : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have ht := (h1.const_mul (W*M)).add
    ((StaticTrialLimit.quadratic_scaled_limit 1 R T γ hγ.ne').const_mul (M^2))
  simp only [mul_zero,add_zero] at ht
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a≤T+R := by
    have hlim := h1.const_mul γ
    simp only [mul_zero] at hlim
    exact (hlim.eventually (gt_mem_nhds (by linarith : 0<T+R))).mono (fun _ ha => ha.le)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hS,hm,hsmall,self_mem_nhdsWithin] with a hS hm hdM ha
  change 0<a at ha
  have hd := mul_pos hγ ha
  have he := hwhole (γ*a) hd hdM (S a) hS
  have hie : Integrable (fun q : Plane => conj ((a : ℂ)⁻¹)*coherentError (S a) A q) := he.1.const_mul _
  have he' : (∫ q : Plane, ‖conj ((a : ℂ)⁻¹)*coherentError (S a) A q‖)≤(W*M)*a := by
    calc
      _ = a⁻¹*(∫ q : Plane, ‖coherentError (S a) A q‖) := by
        simp only [norm_mul,norm_conj,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,integral_const_mul]
      _ ≤ a⁻¹*(W*(M*a^2)) := mul_le_mul_of_nonneg_left
        (he.2.trans (mul_le_mul_of_nonneg_left hm hW)) (inv_nonneg.mpr ha.le)
      _ = _ := by field_simp [ha.ne']; ring
  have hq := PlaneQuadraticFlux.whole_mass 1 R T (γ*a) hR hd hT hTR (S a) (S a) hS hS
  have hq' : (∫ q : Plane, ‖MaxwellPlaneL1.flux 1 (S a) (S a) q‖)≤
      M^2*(PlaneQuadraticFlux.wholeConstant 1 R T (γ*a)*a^4) := by
    have hm0 := sourceMass_nonnegative (S a)
    have hC := PlaneQuadraticFlux.whole_constant_nonnegative 1 R T (γ*a) hR (by linarith) hd
    calc
      _ ≤ PlaneQuadraticFlux.wholeConstant 1 R T (γ*a)*sourceMass (S a)*sourceMass (S a) := hq.2
      _ ≤ PlaneQuadraticFlux.wholeConstant 1 R T (γ*a)*(M*a^2)*(M*a^2) := by gcongr
      _ = _ := by ring
  obtain ⟨_,_,hwholeQ⟩ := MaxwellPlaneL1.whole_plane_bound 1 R (γ*a) hR hd
  have hiq := (hwholeQ (S a) (S a) hS hS).1
  simp_rw [trial_identity]
  calc
    _ ≤ (∫ q : Plane, ‖conj ((a : ℂ)⁻¹)*coherentError (S a) A q‖)+
        (∫ q : Plane, ‖MaxwellPlaneL1.flux 1 (S a) (S a) q‖) := by
      rw [← integral_add hie.norm hiq.norm]
      exact integral_mono_ae (hie.add hiq).norm (hie.norm.add hiq.norm)
        (Filter.Eventually.of_forall (fun q => norm_add_le _ _))
    _ ≤ _ := add_le_add he' hq'

end OQ14.RestrictedTETrialLimit
#print axioms OQ14.RestrictedTETrialLimit.error_smul
#print axioms OQ14.RestrictedTETrialLimit.trial_identity
#print axioms OQ14.RestrictedTETrialLimit.trial_to_static
