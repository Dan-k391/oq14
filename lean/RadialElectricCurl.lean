import RadialNormalPrimitive
import ScalarRadiation

/-! The actual distributional curl of radial polynomial fields with normal jumps. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.RadialElectricCurl
open MeasureTheory Set Filter OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.RadialNormalPrimitive OQ14.ExteriorClassical OQ14.GreenKernel
open scoped Topology

private theorem polynomial_partial_continuous (p : Poly) (i : Fin 3) :
    Continuous (fun x => dcoord (complexEvaluate p) x i) :=
  ((complexEvaluate_regular p).continuous_fderiv (by simp)).clm_apply continuous_const

private theorem polynomial_second_continuous (p : Poly) (i j : Fin 3) :
    Continuous (fun x => dcoord (fun y => dcoord (complexEvaluate p) y j) x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (partial_smooth (partial_smooth (complexEvaluate_regular p).contDiffAt j) i).continuousAt

theorem remainder_partial (a b : ℝ → ℂ) (p : Poly)
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d)
    (hm : StronglyMeasurable (radialDerivative b)) (x : Space) (hx : x≠0)
    (hb : ContinuousAt b ‖x‖) (aD : ℂ) (ha : HasDerivAt a aD ‖x‖) (i j : Fin 3) :
    pd (tangentialRemainder a b p) x i j=
      (a ‖x‖-primitive b ‖x‖)*dcoord (fun y => dcoord (complexEvaluate p) y j) x i+
      ((aD-(‖x‖ : ℂ)*b ‖x‖)*(x i/‖x‖ : ℝ))*dcoord (complexEvaluate p) x j := by
  have hd := ha.sub (primitive_hasDerivAt b hi hm ‖x‖ hb)
  have hcomp : DifferentiableAt ℝ (fun y : Space => a ‖y‖-primitive b ‖y‖) x :=
    hd.differentiableAt.comp x (differentiableAt_id.norm ℝ hx)
  unfold pd tangentialRemainder
  rw [partial_mul hcomp ((partial_smooth (complexEvaluate_regular p).contDiffAt j).differentiableAt (by simp))]
  rw [radial_composition_partial (fun r => a r-primitive b r) _ x hx hd]
  ring

theorem remainder_curl (a b : ℝ → ℂ) (p : Poly)
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d)
    (hm : StronglyMeasurable (radialDerivative b)) (x : Space) (hx : x≠0)
    (hb : ContinuousAt b ‖x‖) (aD : ℂ) (ha : HasDerivAt a aD ‖x‖) (i : Fin 3) :
    curl (tangentialRemainder a b p) x i=
      (b ‖x‖-aD/(‖x‖ : ℂ))*DebyeRadialTrace.angularToroidal p x i := by
  have hc (i j : Fin 3) := partial_comm_at (x := x) (complexEvaluate_regular p).contDiffAt i j
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  fin_cases i <;> dsimp [curl,DebyeRadialTrace.angularToroidal] <;>
    rw [remainder_partial a b p hi hm x hx hb aD ha,
      remainder_partial a b p hi hm x hx hb aD ha,hc] <;>
    push_cast <;> field_simp [hr] <;> ring

private theorem unit_product_locallyIntegrable (f : Space → ℂ) (hf : LocallyIntegrable f) (i : Fin 3) :
    LocallyIntegrable (fun x => f x*(x i/‖x‖ : ℝ)) := by
  have hu : Measurable (fun x : Space => ((x i/‖x‖ : ℝ) : ℂ)) := by fun_prop
  apply hf.mono (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards with x
  change ‖f x*((x i/‖x‖ : ℝ) : ℂ)‖ ≤ ‖f x‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (RadialInterface.coordinate_ratio_norm_le x i)

theorem remainder_partial_locallyIntegrable (a b aD : ℝ → ℂ) (p : Poly) (S : Set ℝ) (hS : S.Countable)
    (ha : ContinuousOn a (Ici 0))
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d)
    (hm : StronglyMeasurable (radialDerivative b))
    (hb : LocallyIntegrable (fun x : Space => b ‖x‖))
    (hD : LocallyIntegrable (fun x : Space => aD ‖x‖))
    (hc : ∀ r, 0 < r → r ∉ S → ContinuousAt b r)
    (hd : ∀ r, 0 < r → r ∉ S → HasDerivAt a (aD r) r) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (tangentialRemainder a b p) x i j) := by
  have hcoeff : Continuous (fun x : Space => a ‖x‖-primitive b ‖x‖) :=
    (ha.comp_continuous continuous_norm (fun x => norm_nonneg x)).sub
      ((primitive_continuous b hi).comp continuous_norm)
  have hnormal : LocallyIntegrable (fun x : Space => (‖x‖ : ℂ)*b ‖x‖) := by
    have h := RadialInterface.locallyIntegrable_mul_continuous (fun x : Space => b ‖x‖)
      (fun x : Space => (‖x‖ : ℂ)) hb (Complex.continuous_ofReal.comp continuous_norm)
    simpa only [mul_comm] using h
  have hfirst : LocallyIntegrable (fun x : Space =>
      (a ‖x‖-primitive b ‖x‖)*dcoord (fun y => dcoord (complexEvaluate p) y j) x i) :=
    (hcoeff.mul (polynomial_second_continuous p i j)).locallyIntegrable
  have hsecond := RadialInterface.locallyIntegrable_mul_continuous _ _
    (unit_product_locallyIntegrable _ (hD.sub hnormal) i) (polynomial_partial_continuous p j)
  apply (hfirst.add hsecond).mono (measurable_fderiv_apply_const ℝ
    (fun x => tangentialRemainder a b p x j) (basis i)).aestronglyMeasurable
  filter_upwards [SphericalInterfaces.ae_off_interfaces S hS,
    show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  change ‖pd (tangentialRemainder a b p) x i j‖ ≤ _
  rw [remainder_partial a b p hi hm x hx0 (hc _ (norm_pos_iff.mpr hx0) hx)
    (aD ‖x‖) (hd _ (norm_pos_iff.mpr hx0) hx)]
  exact le_rfl

theorem electric_weak_curl (a b aD : ℝ → ℂ) (p : Poly) (S : Set ℝ) (hS : S.Countable)
    (ha : ContinuousOn a (Ici 0))
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d)
    (hm : StronglyMeasurable (radialDerivative b))
    (hb : LocallyIntegrable (fun x : Space => b ‖x‖))
    (hD : LocallyIntegrable (fun x : Space => aD ‖x‖))
    (hc : ∀ r, 0 < r → r ∉ S → ContinuousAt b r)
    (hd : ∀ r, 0 < r → r ∉ S → HasDerivAt a (aD r) r)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (electric a b p) φ=fun i =>
      ∫ x, ((b ‖x‖-aD ‖x‖/(‖x‖ : ℂ))*DebyeRadialTrace.angularToroidal p x i)*φ x := by
  rw [electric_weakCurl_eq_remainder a b p S hS ha hi hm hb hc φ hφ hcompact]
  have hdiff (x : Space) (hx0 : x≠0) (hx : ‖x‖ ∉ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun y => tangentialRemainder a b p y j) x := by
    have hv := (hd _ (norm_pos_iff.mpr hx0) hx).sub
      (primitive_hasDerivAt b hi hm ‖x‖ (hc _ (norm_pos_iff.mpr hx0) hx))
    exact (hv.differentiableAt.comp x (differentiableAt_id.norm ℝ hx0)).mul
      ((partial_smooth (complexEvaluate_regular p).contDiffAt j).differentiableAt (by simp))
  rw [← SphericalInterfaces.curl_integration_by_parts S hS _
    (tangentialRemainder_continuous a b p ha hi) hdiff
    (remainder_partial_locallyIntegrable a b aD p S hS ha hi hm hb hD hc hd)
    φ (hφ.of_le (by norm_num)) hcompact]
  ext i
  apply integral_congr_ae
  filter_upwards [SphericalInterfaces.ae_off_interfaces S hS,
    show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  rw [remainder_curl a b p hi hm x hx0 (hc _ (norm_pos_iff.mpr hx0) hx)
    (aD ‖x‖) (hd _ (norm_pos_iff.mpr hx0) hx)]

end OQ14.RadialElectricCurl

#print axioms OQ14.RadialElectricCurl.remainder_partial
#print axioms OQ14.RadialElectricCurl.remainder_curl
#print axioms OQ14.RadialElectricCurl.remainder_partial_locallyIntegrable
#print axioms OQ14.RadialElectricCurl.electric_weak_curl
