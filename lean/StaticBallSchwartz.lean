import StaticBallL2
import NewtonL2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Actual Schwartz weak derivatives of the uniform-ball potential

The spherical interface is removed by the off-countable fundamental theorem
on coordinate lines. Boundary values at infinity vanish by the actual
Schwartz decay and a proved bound on the continuous gradient.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallSchwartz

open MeasureTheory Filter Set Maxwell PointSingularity SphereRemovable
open scoped Topology SchwartzMap

abbrev Space := FourierL2.Space

theorem integral_derivative_off_countable
    (f f' : ℝ → ℂ) (s : Set ℝ) (hs : s.Countable) (hc : Continuous f)
    (hd : ∀ t, t ∉ s → HasDerivAt f (f' t) t) (hi : Integrable f')
    (hb : Tendsto f atBot (𝓝 0)) (ht : Tendsto f atTop (𝓝 0)) :
    (∫ t, f' t) = 0 := by
  have he : ∀ n : ℕ, (∫ t in -(n : ℝ)..(n : ℝ), f' t) = f n - f (-n) := by
    intro n
    exact integral_eq_of_hasDerivWithinAt_off_countable_of_le f f'
      (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hs hc.continuousOn
      (fun t ht => hd t ht.2) hi.intervalIntegrable
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hn
  have hl := intervalIntegral_tendsto_integral hi hm hn
  have hr := (ht.comp hn).sub (hb.comp hm)
  simp only [sub_self] at hr
  exact tendsto_nhds_unique hl (hr.congr (fun n => (he n).symm))

theorem line_norm_ge_abs (i : Fin 3) (q : Plane) (t : ℝ) :
    |t| ≤ ‖(split i).symm (t,q)‖ := by
  have he := join_norm_sq i q t
  have hn := norm_nonneg ((split i).symm (t,q))
  nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_abs t, abs_nonneg t]

theorem line_tendsto_top (i : Fin 3) (q : Plane) :
    Tendsto (fun t : ℝ => (split i).symm (t,q)) atTop (cocompact Space) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : Space)
  simp only [dist_zero_right]
  exact tendsto_atTop_mono (fun t => (le_abs_self t).trans (line_norm_ge_abs i q t)) tendsto_id

theorem line_tendsto_bot (i : Fin 3) (q : Plane) :
    Tendsto (fun t : ℝ => (split i).symm (t,q)) atBot (cocompact Space) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : Space)
  simp only [dist_zero_right]
  exact tendsto_atTop_mono (fun t => (neg_le_abs t).trans (line_norm_ge_abs i q t))
    tendsto_neg_atBot_atTop

theorem schwartz_integration_by_parts (i : Fin 3) (R : ℝ) (f : Space → ℂ)
    (φ : 𝓢(Space, ℂ)) (hc : Continuous f)
    (hf : ∀ x, x ≠ 0 → ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hl : Integrable (fun x => dcoord f x i * φ x))
    (hr : Integrable (fun x => f x * dcoord φ x i)) :
    (∫ x, dcoord f x i * φ x) = -(∫ x, f x * dcoord φ x i) := by
  rw [coordinate_Fubini i _ hl, coordinate_Fubini i _ hr, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(split_integrable i _ hl).prod_left_ae,
    (split_integrable i _ hr).prod_left_ae,
    show ∀ᵐ q : Plane, q ≠ 0 from ae_iff.mpr (by simp)] with q hleft hright hq
  have hbound : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => ‖f ((split i).symm (t,q))‖) :=
    isBoundedUnder_of_eventually_le (a := C) (Filter.Eventually.of_forall (fun t => hC _))
  have hbound' : IsBoundedUnder (· ≤ ·) atBot (fun t : ℝ => ‖f ((split i).symm (t,q))‖) :=
    isBoundedUnder_of_eventually_le (a := C) (Filter.Eventually.of_forall (fun t => hC _))
  have htop : Tendsto (fun t => f ((split i).symm (t,q)) * φ ((split i).symm (t,q)))
      atTop (𝓝 0) :=
    isBoundedUnder_le_mul_tendsto_zero hbound ((zero_at_infty φ).comp (line_tendsto_top i q))
  have hbot : Tendsto (fun t => f ((split i).symm (t,q)) * φ ((split i).symm (t,q)))
      atBot (𝓝 0) :=
    isBoundedUnder_le_mul_tendsto_zero hbound' ((zero_at_infty φ).comp (line_tendsto_bot i q))
  have he := integral_derivative_off_countable
    (fun t => f ((split i).symm (t,q)) * φ ((split i).symm (t,q)))
    (fun t => dcoord f ((split i).symm (t,q)) i * φ ((split i).symm (t,q)) +
      f ((split i).symm (t,q)) * dcoord φ ((split i).symm (t,q)) i)
    {t | ‖(split i).symm (t,q)‖ = R} (coordinate_line_sphere_finite i q R).countable
    ((hc.comp (line_continuous i q)).mul (φ.continuous.comp (line_continuous i q)))
    (fun t ht => ((hf _ (join_ne_zero i q hq t) ht).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t)).mul
      ((φ.differentiable _).hasFDerivAt.comp_hasDerivAt t (join_hasDerivAt i q t)))
    (hleft.add hright) hbot htop
  rw [integral_add hleft hright] at he
  exact eq_neg_of_add_eq_zero_left he

theorem gradient_uniform_bound (R : ℝ) (hR : 0 < R) (j : Fin 3) (x : Space) :
    ‖StaticBallHessian.gradient R j x‖ ≤ R/3 := by
  have hm : StaticBallL2.majorant R x ≤ (R^2)⁻¹ := by
    unfold StaticBallL2.majorant
    exact inv_anti₀ (by positivity) (by nlinarith [le_max_right ‖x‖ R])
  have he : (R^3/3)*(R^2)⁻¹ = R/3 := by field_simp; ring
  exact (StaticBallL2.gradient_bound R hR j x).trans
    ((mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq he)

theorem weak_hessian_schwartz (R : ℝ) (hR : 0 < R) (i j : Fin 3)
    (φ : 𝓢(Space, ℂ)) :
    (∫ x, StaticBallL2.hessianL2 R hR i j x * φ x) =
      -(∫ x, StaticBallL2.gradientL2 R hR j x * GradientProjection.pderivative i φ x) := by
  have hd : (fun x => Maxwell.dcoord (StaticBallHessian.gradient R j) x i) =ᵐ[volume]
      StaticBallHessian.hessian R i j := by
    filter_upwards [RadialInterface.ae_regular R] with x hx
    exact StaticBallHessian.gradient_partial R i j x hx.1 hx.2
  have he : (fun x => StaticBallL2.hessianL2 R hR i j x * φ x) =ᵐ[volume]
      (fun x => dcoord (StaticBallHessian.gradient R j) x i * φ x) := by
    filter_upwards [StaticBallL2.hessianL2_ae R hR i j, hd] with x hx hh
    rw [hx, hh]
  have hg : (fun x => StaticBallL2.gradientL2 R hR j x * GradientProjection.pderivative i φ x)
      =ᵐ[volume] (fun x => StaticBallHessian.gradient R j x * dcoord φ x i) := by
    filter_upwards [StaticBallL2.gradientL2_ae R hR j] with x hx
    rw [hx]; rfl
  rw [integral_congr_ae he, integral_congr_ae hg]
  exact schwartz_integration_by_parts i R (StaticBallHessian.gradient R j) φ
    (StaticBallHessian.gradient_continuous R hR j)
    (fun x hx hn => StaticBallHessian.gradient_differentiableAt R j x hx hn)
    (R/3) (gradient_uniform_bound R hR j)
    ((NewtonL2.scalar_pairing_integrable _ φ).congr he)
    ((NewtonL2.scalar_pairing_integrable _ (GradientProjection.pderivative i φ)).congr hg)

end OQ14.StaticBallSchwartz

#print axioms OQ14.StaticBallSchwartz.integral_derivative_off_countable
#print axioms OQ14.StaticBallSchwartz.line_norm_ge_abs
#print axioms OQ14.StaticBallSchwartz.line_tendsto_top
#print axioms OQ14.StaticBallSchwartz.line_tendsto_bot
#print axioms OQ14.StaticBallSchwartz.schwartz_integration_by_parts
#print axioms OQ14.StaticBallSchwartz.gradient_uniform_bound
#print axioms OQ14.StaticBallSchwartz.weak_hessian_schwartz
