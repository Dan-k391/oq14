import StaticBallPotential
import RadialInterface

/-! # Actual global weak Hessian of the explicit uniform-ball potential -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallHessian

open MeasureTheory Metric Set Filter StaticBallPotential Maxwell GreenKernel ModalDipole
open scoped Topology BigOperators

abbrev Space := FourierL2.Space

def gradient (R : ℝ) (j : Fin 3) (x : Space) : ℂ :=
  (force R ‖x‖ : ℂ) * (x j : ℂ)

def forceD (R r : ℝ) : ℝ := if r ≤ R then 0 else R^3/r^4

def exterior (R r : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  (R^3 : ℂ) * ((x i : ℂ)*(x j : ℂ)/(r : ℂ)^5 -
    (if i=j then 1 else 0 : ℂ)/(3*(r : ℂ)^3))

def hessian (R : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  if ‖x‖ ≤ R then -(if i=j then 1 else 0 : ℂ)/3 else exterior R ‖x‖ i j x

theorem gradient_continuous (R : ℝ) (hR : 0 < R) (j : Fin 3) :
    Continuous (gradient R j) :=
  (Complex.continuous_ofReal.comp ((force_continuous R hR).comp continuous_norm)).mul
    (coordinate j).continuous

theorem force_hasDerivAt (R r : ℝ) (hr : r ≠ 0) (hne : r ≠ R) :
    HasDerivAt (force R) (forceD R r) r := by
  rcases hne.lt_or_lt with hh | hh
  · have he : force R =ᶠ[𝓝 r] fun _ => (-1/3 : ℝ) := by
      filter_upwards [Iio_mem_nhds hh] with t ht
      exact if_pos ht.le
    simpa only [forceD, if_pos hh.le] using (hasDerivAt_const r (-1/3 : ℝ)).congr_of_eventuallyEq he
  · have he : force R =ᶠ[𝓝 r] fun t => -R^3/(3*t^3) := by
      filter_upwards [Ioi_mem_nhds hh] with t ht
      exact if_neg (not_le.mpr ht)
    have hd := (hasDerivAt_const r (-R^3)).div (((hasDerivAt_id r).pow 3).const_mul 3)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))
    have hd' : HasDerivAt (fun t : ℝ => -R^3/(3*t^3)) (R^3/r^4) r := by
      convert hd using 1
      simp only [id_eq]
      field_simp
      ring
    simpa only [forceD, if_neg (not_le.mpr hh)] using hd'.congr_of_eventuallyEq he

theorem gradient_differentiableAt (R : ℝ) (j : Fin 3) (x : Space)
    (hx : x ≠ 0) (hne : ‖x‖ ≠ R) : DifferentiableAt ℝ (gradient R j) x := by
  have hf := (force_hasDerivAt R ‖x‖ (norm_ne_zero_iff.mpr hx) hne).ofReal_comp
  exact ((hf.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt).mul
    (coordinate_differentiableAt x j)

theorem gradient_partial (R : ℝ) (i j : Fin 3) (x : Space)
    (hx : x ≠ 0) (hne : ‖x‖ ≠ R) : dcoord (gradient R j) x i = hessian R i j x := by
  have hf := (force_hasDerivAt R ‖x‖ (norm_ne_zero_iff.mpr hx) hne).ofReal_comp
  have hd := (hf.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  have hd' : DifferentiableAt ℝ (fun y : Space => (force R ‖y‖ : ℂ)) x := hd
  have hc' : DifferentiableAt ℝ (fun y : Space => (y j : ℂ)) x := coordinate_differentiableAt x j
  change dcoord (fun y => (force R ‖y‖ : ℂ) * (y j : ℂ)) x i = _
  rw [partial_mul hd' hc',
    radial_composition_partial (fun r => (force R r : ℂ)) (forceD R ‖x‖ : ℂ) x hx hf,
    coordinate_partial]
  unfold hessian force forceD exterior
  by_cases hinside : ‖x‖ ≤ R
  · simp only [if_pos hinside, Complex.ofReal_zero, zero_mul, zero_add]
    push_cast
    ring
  · simp only [if_neg hinside]
    have hxn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    push_cast
    field_simp
    split_ifs <;> ring

theorem clipped_exterior_continuous (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    Continuous (fun x => exterior R (max ‖x‖ (R/2)) i j x) := by
  have hr : Continuous (fun x : Space => ((max ‖x‖ (R/2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_norm.max continuous_const)
  have hn (x : Space) : ((max ‖x‖ (R/2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (half_pos hR) (le_max_right ‖x‖ (R/2))).ne'
  exact continuous_const.mul ((((coordinate i).continuous.mul (coordinate j).continuous).div
    (hr.pow 5) (fun x => pow_ne_zero 5 (hn x))).sub
      (continuous_const.div (continuous_const.mul (hr.pow 3))
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 3 (hn x)))))

theorem hessian_locallyIntegrable (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    LocallyIntegrable (hessian R i j) := by
  let A : ℂ := -(if i=j then 1 else 0 : ℂ)/3
  let B : Space → ℂ := fun x => exterior R (max ‖x‖ (R/2)) i j x
  have hB : Continuous B := clipped_exterior_continuous R hR i j
  have he : hessian R i j = fun x => if ‖x‖ ≤ R then A else B x := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · simp only [hessian, if_pos hx, A]
    · have hh : R/2 ≤ ‖x‖ := by linarith [norm_nonneg x]
      simp only [hessian, if_neg hx, B, max_eq_left hh]
  have hm : Measurable (hessian R i j) := by
    rw [he]
    exact Measurable.ite (isClosed_le continuous_norm continuous_const).measurableSet
      measurable_const hB.measurable
  have hA : Continuous (fun _ : Space => A) := continuous_const
  apply ((hA.norm.add hB.norm).locallyIntegrable).mono hm.aestronglyMeasurable
  filter_upwards with x
  rw [congrFun he x]
  change ‖if ‖x‖ ≤ R then A else B x‖ ≤ ‖‖A‖ + ‖B x‖‖
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  split_ifs <;> linarith [norm_nonneg A, norm_nonneg (B x)]

theorem weak_hessian (R : ℝ) (hR : 0 < R) (i j : Fin 3)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, hessian R i j x * φ x) = -(∫ x, gradient R j x * dcoord φ x i) :=
  RadialInterface.weak_partial i R (gradient R j) (hessian R i j)
    (gradient_continuous R hR j) (fun x hx hn => gradient_differentiableAt R j x hx hn)
    (fun x hx hn => gradient_partial R i j x hx hn) (hessian_locallyIntegrable R hR i j) φ hφ hc

def potentialC (R : ℝ) (x : Space) : ℂ := (potential R x : ℂ)

theorem potentialC_contDiff_one (R : ℝ) (hR : 0 < R) : ContDiff ℝ 1 (potentialC R) :=
  Complex.ofRealCLM.contDiff.comp (potential_contDiff_one R hR)

theorem potentialC_partial (R : ℝ) (hR : 0 < R) (x : Space) (j : Fin 3) :
    dcoord (potentialC R) x j = gradient R j x := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (potential_hasFDerivAt R hR x)
  have hd' : HasFDerivAt (potentialC R)
      (Complex.ofRealCLM.comp (force R ‖x‖ • innerSL ℝ x)) x := hd
  change (fderiv ℝ (potentialC R) x) (basis j) = _
  rw [hd'.fderiv]
  simp [gradient, ContinuousLinearMap.comp_apply, innerSL_apply, basis,
    EuclideanSpace.inner_single_right, Complex.ofReal_mul]

theorem weak_hessian_pairing (R : ℝ) (hR : 0 < R) (i j : Fin 3)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, hessian R i j x * φ x) =
      ∫ x, potentialC R x * dcoord (fun y => dcoord φ y i) x j := by
  rw [weak_hessian R hR i j φ (hφ.of_le (by norm_num)) hc]
  have hp : ContDiff ℝ 1 (fun x => dcoord φ x i) := KernelSource.partial_contDiff hφ i
  have hi := partial_integration_by_parts (potentialC_contDiff_one R hR) hp
    (hc.fderiv_apply ℝ (basis i)) j
  simp_rw [potentialC_partial R hR] at hi
  rw [hi, neg_neg]

theorem coordinate_square_sum (x : Space) :
    (∑ i : Fin 3, (x i : ℂ)^2) = (‖x‖ : ℂ)^2 := by
  have hr : (∑ i : Fin 3, (x i)^2) = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x).symm
  exact_mod_cast hr

theorem exterior_trace (R : ℝ) (x : Space) (hx : x ≠ 0) :
    (∑ j : Fin 3, exterior R ‖x‖ j j x) = 0 := by
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have he : (∑ j : Fin 3, exterior R ‖x‖ j j x) =
      (R^3 : ℂ) * ((∑ j : Fin 3, (x j : ℂ)^2)/(‖x‖ : ℂ)^5 - 1/(‖x‖ : ℂ)^3) := by
    simp [exterior, Fin.sum_univ_three]
    ring
  rw [he, coordinate_square_sum]
  field_simp
  ring

theorem trace_ae (R : ℝ) :
    (fun x => ∑ j : Fin 3, hessian R j j x) =ᵐ[volume]
      fun x => -(ball (0 : Space) R).indicator (fun _ => (1 : ℂ)) x := by
  filter_upwards [RadialInterface.ae_regular R] with x hx
  by_cases hi : ‖x‖ ≤ R
  · have hb : x ∈ ball (0 : Space) R := by
      simpa only [mem_ball, dist_zero_right] using lt_of_le_of_ne hi hx.2
    simp [hessian, hi, hb, Fin.sum_univ_three]
    norm_num
  · have hb : x ∉ ball (0 : Space) R := by
      simpa only [mem_ball, dist_zero_right, not_lt] using (lt_of_not_ge hi).le
    simp only [hessian, if_neg hi, indicator_of_not_mem hb, Pi.zero_apply, neg_zero]
    exact exterior_trace R x hx.1

/-- Global distributional Poisson source, including the spherical interface. -/
theorem weak_laplacian (R : ℝ) (hR : 0 < R) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∑ j : Fin 3, ∫ x, potentialC R x * dcoord (fun y => dcoord φ y j) x j) =
      -(∫ x in ball (0 : Space) R, φ x) := by
  simp_rw [← weak_hessian_pairing R hR _ _ φ hφ hc]
  rw [← integral_finset_sum _ (fun j _ => PointSingularity.test_product_integrable
    (hessian R j j) φ (hessian_locallyIntegrable R hR j j) hφ.continuous hc)]
  have he : (∫ x, ∑ j : Fin 3, hessian R j j x * φ x) =
      ∫ x, -(ball (0 : Space) R).indicator φ x := by
    apply integral_congr_ae
    filter_upwards [trace_ae R] with x hx
    rw [← Finset.sum_mul, hx]
    by_cases hb : x ∈ ball (0 : Space) R <;> simp [hb]
  rw [he, integral_neg, integral_indicator measurableSet_ball]

end OQ14.StaticBallHessian

#print axioms OQ14.StaticBallHessian.gradient_continuous
#print axioms OQ14.StaticBallHessian.force_hasDerivAt
#print axioms OQ14.StaticBallHessian.gradient_differentiableAt
#print axioms OQ14.StaticBallHessian.gradient_partial
#print axioms OQ14.StaticBallHessian.clipped_exterior_continuous
#print axioms OQ14.StaticBallHessian.hessian_locallyIntegrable
#print axioms OQ14.StaticBallHessian.weak_hessian
#print axioms OQ14.StaticBallHessian.potentialC_contDiff_one
#print axioms OQ14.StaticBallHessian.potentialC_partial
#print axioms OQ14.StaticBallHessian.weak_hessian_pairing
#print axioms OQ14.StaticBallHessian.coordinate_square_sum
#print axioms OQ14.StaticBallHessian.exterior_trace
#print axioms OQ14.StaticBallHessian.trace_ae
#print axioms OQ14.StaticBallHessian.weak_laplacian
