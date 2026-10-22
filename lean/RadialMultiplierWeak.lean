import RadialElectricCurl

/-! Actual weak curls of continuous radial multipliers across spherical interfaces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.RadialMultiplierWeak
open MeasureTheory Set Filter OQ14.Maxwell OQ14.ExteriorClassical OQ14.GreenKernel
open scoped Topology

def field (a : ℝ → ℂ) (P : Field) : Field := fun x j => a ‖x‖*P x j

theorem field_partial (a : ℝ → ℂ) (P : Field) (x : Space) (hx : x≠0)
    (aD : ℂ) (ha : HasDerivAt a aD ‖x‖)
    (hP : ∀ j,DifferentiableAt ℝ (fun y => P y j) x) (i j : Fin 3) :
    pd (field a P) x i j=aD*(x i/‖x‖ : ℝ)*P x j+a ‖x‖*pd P x i j := by
  unfold pd field
  have hd : DifferentiableAt ℝ (fun y : Space => a ‖y‖) x :=
    ha.differentiableAt.comp x (differentiableAt_id.norm ℝ hx)
  rw [partial_mul hd (hP j),
    radial_composition_partial a aD x hx ha]
  ring

theorem partial_locallyIntegrable (a aD : ℝ → ℂ) (P : Field) (S : Set ℝ) (hS : S.Countable)
    (ha : Continuous a) (hP : ∀ j,ContDiff ℝ 1 (fun x => P x j))
    (hD : LocallyIntegrable (fun x : Space => aD ‖x‖))
    (hd : ∀ r,0<r → r∉S → HasDerivAt a (aD r) r) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (field a P) x i j) := by
  have hu : Measurable (fun x : Space => ((x i/‖x‖ : ℝ) : ℂ)) := by fun_prop
  have hi : LocallyIntegrable (fun x : Space => aD ‖x‖*(x i/‖x‖ : ℝ)) := by
    apply hD.mono (hD.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    filter_upwards with x
    change ‖aD ‖x‖*((x i/‖x‖ : ℝ) : ℂ)‖ ≤ ‖aD ‖x‖‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (RadialInterface.coordinate_ratio_norm_le x i)
  have hp := RadialInterface.locallyIntegrable_mul_continuous _ _ hi (hP j).continuous
  have hq : Continuous (fun x => a ‖x‖*pd P x i j) :=
    (ha.comp continuous_norm).mul (partial_continuous (hP j) i)
  apply (hp.add hq.locallyIntegrable).mono
    (measurable_fderiv_apply_const ℝ (fun x => field a P x j) (basis i)).aestronglyMeasurable
  filter_upwards [SphericalInterfaces.ae_off_interfaces S hS,
    show ∀ᵐ x : Space,x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  change ‖pd (field a P) x i j‖ ≤ _
  rw [field_partial a P x hx0 (aD ‖x‖) (hd _ (norm_pos_iff.mpr hx0) hx)
    (fun j => (hP j).differentiable le_rfl x)]
  exact le_rfl

theorem weak_curl (a aD : ℝ → ℂ) (P : Field) (S : Set ℝ) (hS : S.Countable)
    (ha : Continuous a) (hP : ∀ j,ContDiff ℝ 1 (fun x => P x j))
    (hD : LocallyIntegrable (fun x : Space => aD ‖x‖))
    (hd : ∀ r,0<r → r∉S → HasDerivAt a (aD r) r)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (field a P) φ=fun j => ∫ x,curl (field a P) x j*φ x := by
  symm
  apply SphericalInterfaces.curl_integration_by_parts S hS
    (field a P) (fun j => (ha.comp continuous_norm).mul (hP j).continuous)
    (fun x hx0 hx j => ((hd _ (norm_pos_iff.mpr hx0) hx).differentiableAt.comp x
      (differentiableAt_id.norm ℝ hx0)).mul ((hP j).differentiable le_rfl x))
    (partial_locallyIntegrable a aD P S hS ha hP hD hd) φ hφ hc

end OQ14.RadialMultiplierWeak

#print axioms OQ14.RadialMultiplierWeak.field_partial
#print axioms OQ14.RadialMultiplierWeak.partial_locallyIntegrable
#print axioms OQ14.RadialMultiplierWeak.weak_curl
