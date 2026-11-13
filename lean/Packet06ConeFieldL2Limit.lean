import Packet06ConeProfileBounds
import Packet06ConeFieldLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeFieldL2Limit
open MeasureTheory Filter Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere

theorem angular_electric_square_integral_tendsto (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hbound : ∀ j, ell j ∈ Ioo (0 : ℝ) 2) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun j => ∫ q : Sphere,
      ‖t⁻¹ • ConicalCapField.angularElectric (CapAngularShooting.exponent (ell j)) (ell j) t q - basis 2‖^2 ∂angularMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,huniform⟩ := Packet06ConeProfileBounds.profile_slope_uniform t ht ht1
  let F : ℕ → Sphere → Space := fun j q =>
    t⁻¹ • ConicalCapField.angularElectric (CapAngularShooting.exponent (ell j)) (ell j) t q - basis 2
  let M : ℝ := t⁻¹*(2*C)+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hboundF (j : ℕ) (q : Sphere) : ‖F j q‖ ≤ M := by
    have hν := (CapAngularShooting.exponent_range (ell j) (hbound j))
    have hq : ‖(q : Space)‖ = 1 := sphere_norm q
    have htangent := tangent_norm_le q
    have hs := huniform (ell j) ⟨(hbound j).1.le,(hbound j).2.le⟩ ((q : Space) 2) (SphereCapWeak.coordinate_range q)
    have hfield : ‖field (ell j) t q‖ ≤ C := by simpa [field,Real.norm_eq_abs] using hs.1
    have hslope : ‖CapSturmLiouville.slope (ell j) t ((q : Space) 2)‖ ≤ C := by simpa [Real.norm_eq_abs] using hs.2
    have hνn : ‖CapAngularShooting.exponent (ell j)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs,abs_of_pos hν.1] using hν.2.le
    have hbasis : ‖(basis 2 : Space)‖ = 1 := by simp [basis]
    have hgrad : ‖SphereCapH1.gradient (ell j) t q‖ ≤ C := by
      rw [SphereCapH1.gradient,norm_smul]
      calc
        _ ≤ C*1 := mul_le_mul hslope htangent (norm_nonneg _) hC
        _ = C := by ring
    have he : ‖ConicalCapField.angularElectric (CapAngularShooting.exponent (ell j)) (ell j) t q‖ ≤ 2*C := by
      unfold ConicalCapField.angularElectric
      calc
        _ ≤ ‖(CapAngularShooting.exponent (ell j)*field (ell j) t q) • (q : Space)‖ + ‖SphereCapH1.gradient (ell j) t q‖ := norm_add_le _ _
        _ ≤ C+C := by
          rw [norm_smul,norm_mul,hq,mul_one]
          have hp := mul_le_mul hνn hfield (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
          simpa using add_le_add hp hgrad
        _ = 2*C := by ring
    change ‖t⁻¹ • ConicalCapField.angularElectric _ _ t q - basis 2‖ ≤ M
    calc
      _ ≤ ‖t⁻¹ • ConicalCapField.angularElectric (CapAngularShooting.exponent (ell j)) (ell j) t q‖ + ‖(basis 2 : Space)‖ := norm_sub_le _ _
      _ ≤ t⁻¹*(2*C)+1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),hbasis]
        exact add_le_add_right (mul_le_mul_of_nonneg_left he (inv_pos.mpr ht).le) 1
      _ = M := rfl
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun q : Sphere => ‖F j q‖^2) angularMeasure := by
    have hfield := (field_memLp (ell j) t ⟨(hbound j).1.le,(hbound j).2.le⟩ ht ht1 2).aestronglyMeasurable
    have hgrad := (gradient_memLp (ell j) t ⟨(hbound j).1.le,(hbound j).2.le⟩ ht ht1 2).aestronglyMeasurable
    have hq : AEStronglyMeasurable (fun q : Sphere => (q : Space)) angularMeasure := continuous_subtype_val.aestronglyMeasurable
    have hE : AEStronglyMeasurable (fun q : Sphere => ConicalCapField.angularElectric
        (CapAngularShooting.exponent (ell j)) (ell j) t q) angularMeasure :=
      ((hfield.const_mul _).smul hq).add hgrad
    have hF : AEStronglyMeasurable (F j) angularMeasure := by
      change AEStronglyMeasurable (fun q : Sphere => t⁻¹ • ConicalCapField.angularElectric _ _ t q - basis 2) angularMeasure
      exact (hE.const_smul (t⁻¹ : ℝ)).sub aestronglyMeasurable_const
    exact hF.norm.pow 2
  have hdom : Integrable (fun _ : Sphere => M^2) angularMeasure := integrable_const _
  have hpoint : ∀ᵐ q : Sphere ∂angularMeasure, Tendsto (fun j => ‖F j q‖^2) atTop (𝓝 0) := by
    filter_upwards with q
    have h := Packet06ConeFieldLimit.normalized_angular_electric_tendsto ell hell
      (fun j => ⟨(hbound j).1.le,(hbound j).2.le⟩) t ht ht1 q
    simpa only [F,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using (h.sub_const (basis 2)).norm.pow 2
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Sphere => M^2)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall (fun j => ae_of_all _ (fun q => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hboundF j q) 2))) hdom hpoint
  simpa only [F,integral_zero] using h
#print axioms OQ14.Packet06ConeFieldL2Limit.angular_electric_square_integral_tendsto
end OQ14.Packet06ConeFieldL2Limit
