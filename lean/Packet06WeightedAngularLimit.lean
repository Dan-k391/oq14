import Packet06ConeUniformWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedAngularLimit
open Filter Set MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalMomentWeights
open scoped Topology

theorem tangent_square_integral_tendsto (ell d : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hd : Tendsto d atTop (𝓝 0)) (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2)
    (D : ℝ) (hD : 0 ≤ D) (hdBound : ∀ j, d j ∈ Icc (0 : ℝ) D)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    Tendsto (fun j => ∫ q : Sphere,
      ‖((t⁻¹ : ℝ) : ℂ)*tangent (ell j) (d j) t i q -
        (((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ)‖^2 ∂angularMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hweights⟩ := Packet06ConeUniformWeights.uniform_weights t D ht ht1 hD
  let F : ℕ → Sphere → ℂ := fun j q => ((t⁻¹ : ℝ) : ℂ)*tangent (ell j) (d j) t i q -
    (((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ)
  let M : ℝ := t⁻¹*C+1
  have hboundF (j : ℕ) (q : Sphere) : ‖F j q‖ ≤ M := by
    have htang : ‖(basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i‖ ≤ 1 :=
      (PiLp.norm_apply_le _ i).trans (SphereCapH1.tangent_norm_le q)
    calc
      _ ≤ ‖((t⁻¹ : ℝ) : ℂ)*tangent (ell j) (d j) t i q‖ +
          ‖(((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ t⁻¹*C+1 := by
        rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hweights _ (hbound j) _ (hdBound j) i q).2 (inv_pos.mpr ht).le) htang
      _ = M := rfl
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun q : Sphere => ‖F j q‖^2) angularMeasure := by
    have htan : AEStronglyMeasurable (tangent (ell j) (d j) t i) angularMeasure :=
      (tangent_measurable _ _ _ (hbound j) ht ht1 i).aestronglyMeasurable
    have hq : Continuous (fun q : Sphere => (((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ)) := by
      exact Complex.continuous_ofReal.comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp
        (continuous_const.sub ((OQ14.ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val)))
    exact ((htan.const_mul _).sub hq.aestronglyMeasurable).norm.pow 2
  have hdom : Integrable (fun _ : Sphere => M^2) angularMeasure := integrable_const _
  have hpoint : ∀ᵐ q : Sphere ∂angularMeasure, Tendsto (fun j => ‖F j q‖^2) atTop (𝓝 0) := by
    filter_upwards with q
    have hz := SphereCapWeak.coordinate_range q
    have hs := Packet06ConeGradientLimit.normalized_slope_tendsto ell hell hbound t ((q : Maxwell.Space) 2) ht ht1 hz.1 hz.2
    have hcoef : Tendsto (fun j => CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2)) atTop (𝓝 1) := by
      unfold CapSturmLiouville.coefficient
      split_ifs
      · exact tendsto_const_nhds
      · simpa using tendsto_const_nhds.add hd
    have hprod := hcoef.mul hs
    have hsc : Tendsto (fun j => CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2) *
      (CapSturmLiouville.slope (ell j) t ((q : Maxwell.Space) 2)/t)) atTop (𝓝 1) := by simpa using hprod
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hsc
    have he : (fun j => F j q) = fun j =>
      (((CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2) *
        (CapSturmLiouville.slope (ell j) t ((q : Maxwell.Space) 2)/t) : ℝ) : ℂ)-1)*
          (((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ) := by
      funext j
      simp only [F,tangent,SphereCapH1.gradient,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div]
      push_cast
      ring
    have hF : Tendsto (fun j => F j q) atTop (𝓝 0) := by
      rw [he]
      simpa using ((hc.sub_const 1).mul_const
      (((basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i : ℝ) : ℂ))
    simpa using hF.norm.pow 2
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Sphere => M^2)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall (fun j => ae_of_all _ (fun q => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hboundF j q) 2))) hdom hpoint
  simpa only [F,integral_zero] using h
#print axioms OQ14.Packet06WeightedAngularLimit.tangent_square_integral_tendsto
end OQ14.Packet06WeightedAngularLimit
