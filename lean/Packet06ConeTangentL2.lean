import Packet06ConeFieldL2Limit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeTangentL2
open MeasureTheory Filter Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere

theorem gradient_square_integral_tendsto (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun j => ∫ q : Sphere,
      ‖t⁻¹ • SphereCapH1.gradient (ell j) t q - (basis 2 - ((q : Space) 2) • (q : Space))‖^2 ∂angularMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,huniform⟩ := Packet06ConeProfileBounds.profile_slope_uniform t ht ht1
  let F : ℕ → Sphere → Space := fun j q =>
    t⁻¹ • SphereCapH1.gradient (ell j) t q - (basis 2 - ((q : Space) 2) • (q : Space))
  let M : ℝ := t⁻¹*C+1
  have hboundF (j : ℕ) (q : Sphere) : ‖F j q‖ ≤ M := by
    have hs := (huniform (ell j) (hbound j) ((q : Space) 2) (SphereCapWeak.coordinate_range q)).2
    have hs' : ‖CapSturmLiouville.slope (ell j) t ((q : Space) 2)‖ ≤ C := by simpa [Real.norm_eq_abs] using hs
    have htangent := tangent_norm_le q
    have hgrad : ‖SphereCapH1.gradient (ell j) t q‖ ≤ C := by
      rw [SphereCapH1.gradient,norm_smul]
      calc
        _ ≤ C*1 := mul_le_mul hs' htangent (norm_nonneg _) hC
        _ = C := by ring
    change ‖t⁻¹ • SphereCapH1.gradient (ell j) t q - (basis 2 - ((q : Space) 2) • (q : Space))‖ ≤ M
    calc
      _ ≤ ‖t⁻¹ • SphereCapH1.gradient (ell j) t q‖ + ‖basis 2 - ((q : Space) 2) • (q : Space)‖ := norm_sub_le _ _
      _ ≤ t⁻¹*C+1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
        exact add_le_add (mul_le_mul_of_nonneg_left hgrad (inv_pos.mpr ht).le) htangent
      _ = M := rfl
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun q : Sphere => ‖F j q‖^2) angularMeasure := by
    have hgrad := (gradient_memLp (ell j) t (hbound j) ht ht1 2).aestronglyMeasurable
    have hq : Continuous (fun q : Sphere => basis 2 - ((q : Space) 2) • (q : Space)) :=
      continuous_const.sub ((OQ14.ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val)
    have hF : AEStronglyMeasurable (F j) angularMeasure :=
      (hgrad.const_smul (t⁻¹ : ℝ)).sub hq.aestronglyMeasurable
    exact hF.norm.pow 2
  have hdom : Integrable (fun _ : Sphere => M^2) angularMeasure := integrable_const _
  have hpoint : ∀ᵐ q : Sphere ∂angularMeasure, Tendsto (fun j => ‖F j q‖^2) atTop (𝓝 0) := by
    filter_upwards with q
    have hz := SphereCapWeak.coordinate_range q
    have hs := Packet06ConeGradientLimit.normalized_slope_tendsto ell hell hbound t ((q : Space) 2) ht ht1 hz.1 hz.2
    have htend := hs.smul (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => basis 2 - ((q : Space) 2) • (q : Space)) atTop
      (𝓝 (basis 2 - ((q : Space) 2) • (q : Space))))
    have he : (fun j => t⁻¹ • SphereCapH1.gradient (ell j) t q) =
        fun j => (CapSturmLiouville.slope (ell j) t ((q : Space) 2)/t) •
          (basis 2 - ((q : Space) 2) • (q : Space)) := by
      funext j
      simp only [SphereCapH1.gradient,smul_smul,div_eq_mul_inv]
      congr 1
      ring
    rw [←he] at htend
    simpa only [F,one_smul,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (htend.sub_const (basis 2 - ((q : Space) 2) • (q : Space))).norm.pow 2
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Sphere => M^2)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall (fun j => ae_of_all _ (fun q => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hboundF j q) 2))) hdom hpoint
  simpa only [F,integral_zero] using h
#print axioms OQ14.Packet06ConeTangentL2.gradient_square_integral_tendsto
end OQ14.Packet06ConeTangentL2
