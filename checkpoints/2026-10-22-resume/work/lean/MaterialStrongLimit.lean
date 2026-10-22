import StaticCoefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Genuine strong L2 continuity of material square-root multiplication. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.MaterialStrongLimit
open MeasureTheory Filter OQ14.StaticCoefficient
open scoped Topology InnerProductSpace

theorem vector_norm_sq_integral (f : VectorL2) : ‖f‖^2=∫ x, ‖f x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow,RCLike.ofReal_re])

theorem sqrtMultiplier_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x))) (f : VectorL2) :
    Tendsto (fun n => sqrtMultiplier (c n) f) atTop (𝓝 (sqrtMultiplier c₀ f)) := by
  let q : ℕ → Space → Vector := fun n x => ((Real.sqrt ((c n).value x) : ℂ)-(Real.sqrt (c₀.value x) : ℂ)) • f x
  have hbound (n : ℕ) (x : Space) : ‖q n x‖ ≤ 2*Real.sqrt D*‖f x‖ := by
    change ‖((Real.sqrt ((c n).value x) : ℂ)-(Real.sqrt (c₀.value x) : ℂ)) • f x‖ ≤ _
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_sub_le _ _).trans
    have h₁ := (sqrt_value_bound (c n) x).trans (Real.sqrt_le_sqrt (hb n))
    have h₂ := (sqrt_value_bound c₀ x).trans (Real.sqrt_le_sqrt hb₀)
    linarith
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖q n x‖^2) (volume : Measure Space) := by
    have h₁ := Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp (c n).measurable)
    have h₀ := Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp c₀.measurable)
    exact ((h₁.sub h₀).aestronglyMeasurable.smul (Lp.memLp f).aestronglyMeasurable).norm.pow 2
  have hi : Integrable (fun x : Space => (2*Real.sqrt D*‖f x‖)^2) := by
    apply (((Lp.memLp f).norm.integrable_sq).const_mul ((2*Real.sqrt D)^2)).congr
    filter_upwards with x
    ring
  have hlim : Tendsto (fun n => ∫ x : Space, ‖q n x‖^2) atTop (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (fun x : Space => (2*Real.sqrt D*‖f x‖)^2)
      (Filter.Eventually.of_forall hm) (Filter.Eventually.of_forall (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound n x) 2))) hi (ha.mono (fun x hx => by
          have ht := (((Complex.continuous_ofReal.tendsto _).comp hx.sqrt).sub_const
            (Real.sqrt (c₀.value x) : ℂ)).smul_const (f x) |>.norm.pow 2
          simpa only [q,sub_self,zero_smul,norm_zero,zero_pow (by decide : 2≠0)] using ht))
    simpa only [integral_zero] using hh
  have hnorm (n : ℕ) : ‖sqrtMultiplier (c n) f-sqrtMultiplier c₀ f‖^2=∫ x : Space, ‖q n x‖^2 := by
    rw [vector_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (sqrtMultiplier (c n) f) (sqrtMultiplier c₀ f),
      sqrtMultiplier_ae (c n) f,sqrtMultiplier_ae c₀ f] with x hs hn h₀
    rw [hs]
    change ‖sqrtMultiplier (c n) f x-sqrtMultiplier c₀ f x‖^2=_
    rw [hn,h₀,← sub_smul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (hlim.congr' (Filter.Eventually.of_forall (fun n => (hnorm n).symm))).sqrt
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

theorem sqrtMultiplier_varying_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (f : ℕ → VectorL2) (f₀ : VectorL2) (hf : Tendsto f atTop (𝓝 f₀)) :
    Tendsto (fun n => sqrtMultiplier (c n) (f n)) atTop (𝓝 (sqrtMultiplier c₀ f₀)) := by
  have hfixed := sqrtMultiplier_tendsto c c₀ D hb hb₀ ha f₀
  have hbound (n : ℕ) : ‖sqrtMultiplier (c n) (f n)-sqrtMultiplier c₀ f₀‖ ≤
      Real.sqrt D*‖f n-f₀‖+‖sqrtMultiplier (c n) f₀-sqrtMultiplier c₀ f₀‖ := by
    have he : sqrtMultiplier (c n) (f n)-sqrtMultiplier c₀ f₀=
        sqrtMultiplier (c n) (f n-f₀)+(sqrtMultiplier (c n) f₀-sqrtMultiplier c₀ f₀) := by rw [map_sub]; abel
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add_right
    exact ((sqrtMultiplier (c n)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((sqrtMultiplier_norm_le (c n)).trans (Real.sqrt_le_sqrt (hb n))) (norm_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hl : Tendsto (fun n => Real.sqrt D*‖f n-f₀‖+‖sqrtMultiplier (c n) f₀-sqrtMultiplier c₀ f₀‖) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hf)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hfixed)
  exact squeeze_zero (fun n => norm_nonneg _) hbound hl

end OQ14.MaterialStrongLimit


#print axioms OQ14.MaterialStrongLimit.vector_norm_sq_integral
#print axioms OQ14.MaterialStrongLimit.sqrtMultiplier_tendsto
#print axioms OQ14.MaterialStrongLimit.sqrtMultiplier_varying_tendsto
