import SphereAngularSymmetry

/-! A genuine cap-weighted coordinate trial on the Euclidean unit sphere.
This establishes the strict variational estimate, without an eigenvalue-existence assertion. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ConicalAngularTrial
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereAngularSymmetry
open scoped InnerProductSpace

def coordinate (i : Fin 3) (n : Sphere) : ℝ := (n : Space) i

theorem coordinate_continuous (i : Fin 3) : Continuous (coordinate i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_subtype_val

theorem continuous_integrable (f : Sphere → ℝ) (hf : Continuous f) :
    Integrable f angularMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def permutation (e : Equiv.Perm (Fin 3)) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

theorem coordinate_permutation (e : Equiv.Perm (Fin 3)) (i : Fin 3) (n : Sphere) :
    coordinate i (sphereMap (permutation e) n) = coordinate (e.symm i) n := rfl

theorem square_integral_eq (i j : Fin 3) :
    (∫ n, coordinate i n ^ 2 ∂angularMeasure) = ∫ n, coordinate j n ^ 2 ∂angularMeasure := by
  have h := integral_sphereMap (permutation (Equiv.swap i j)) (fun n => coordinate i n ^ 2)
  simpa only [coordinate_permutation, Equiv.symm_swap, Equiv.swap_apply_left] using h.symm

theorem coordinate_squares (n : Sphere) : ∑ i : Fin 3, coordinate i n ^ 2 = 1 := by
  have h := n.property
  change (n : Space) ∈ Metric.sphere (0 : Space) 1 at h
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at h
  simpa [coordinate] using h

theorem unweighted_balance (i : Fin 3) :
    (∫ n, (1 - 3 * coordinate i n ^ 2) ∂angularMeasure) = 0 := by
  have hi (j : Fin 3) : Integrable (fun n => coordinate j n ^ 2) angularMeasure :=
    continuous_integrable _ ((coordinate_continuous j).pow 2)
  have hs : (∫ n, (1 : ℝ) ∂angularMeasure) =
      ∑ j : Fin 3, ∫ n, coordinate j n ^ 2 ∂angularMeasure := by
    rw [← integral_finset_sum _ (fun j _ => hi j)]
    apply integral_congr_ae
    filter_upwards with n
    exact (coordinate_squares n).symm
  have he : (∫ n, (1 : ℝ) ∂angularMeasure) =
      3 * ∫ n, coordinate i n ^ 2 ∂angularMeasure := by
    rw [hs]
    simp_rw [square_integral_eq _ i]
    simp [Fin.sum_univ_three]
  rw [integral_sub (integrable_const _) ((hi i).const_mul _), integral_const_mul, he]
  ring

def cap (t : ℝ) : Set Sphere := {n | t < |coordinate 2 n|}
def weight (d t : ℝ) (n : Sphere) : ℝ := 1 + d * (cap t).indicator (fun _ => 1) n
def tangentGradient (i : Fin 3) (n : Sphere) : Space := basis i - coordinate i n • (n : Space)

theorem tangentGradient_inner (i : Fin 3) (n : Sphere) :
    ⟪(n : Space), tangentGradient i n⟫_ℝ = 0 := by
  rw [tangentGradient, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    sphere_norm]
  simp [coordinate, basis, EuclideanSpace.inner_single_right]

theorem tangentGradient_norm_sq (i : Fin 3) (n : Sphere) :
    ‖tangentGradient i n‖ ^ 2 = 1 - coordinate i n ^ 2 := by
  rw [tangentGradient, norm_sub_sq_real]
  simp [basis, EuclideanSpace.inner_single_left, coordinate, norm_smul, sphere_norm,
    sq_abs]
  ring

theorem cap_open (t : ℝ) : IsOpen (cap t) :=
  isOpen_lt continuous_const (coordinate_continuous 2).abs

theorem weighted_integrable (d t : ℝ) (f : Sphere → ℝ) (hf : Continuous f) :
    Integrable (fun n => weight d t n * f n) angularMeasure := by
  have hi := continuous_integrable f hf
  have hc := hi.indicator (cap_open t).measurableSet
  have he : (fun n => weight d t n * f n) = f + d • (cap t).indicator f := by
    funext n
    by_cases hn : n ∈ cap t
    · simp only [weight, indicator_of_mem hn, mul_one, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    · simp [weight, hn]
  rw [he]
  exact hi.add (hc.smul d)

theorem weighted_integral (d t : ℝ) (f : Sphere → ℝ) (hf : Continuous f) :
    (∫ n, weight d t n * f n ∂angularMeasure) =
      (∫ n, f n ∂angularMeasure) + d * ∫ n in cap t, f n ∂angularMeasure := by
  have hi := continuous_integrable f hf
  have he : (fun n => weight d t n * f n) =
      (fun n => f n + d * (cap t).indicator f n) := by
    funext n
    by_cases hn : n ∈ cap t
    · simp only [weight, indicator_of_mem hn, mul_one]
      ring
    · simp [weight, hn]
  rw [he, integral_add hi ((hi.indicator (cap_open t).measurableSet).const_mul d),
    integral_const_mul, integral_indicator (cap_open t).measurableSet]

theorem coordinate_neg (i : Fin 3) (n : Sphere) :
    coordinate i (sphereMap (LinearIsometryEquiv.neg ℝ) n) = -coordinate i n := rfl

theorem weight_neg (d t : ℝ) (n : Sphere) :
    weight d t (sphereMap (LinearIsometryEquiv.neg ℝ) n) = weight d t n := by
  have he : sphereMap (LinearIsometryEquiv.neg ℝ) n ∈ cap t ↔ n ∈ cap t := by
    simp only [cap, mem_setOf_eq, coordinate_neg, abs_neg]
  by_cases hn : n ∈ cap t <;> simp [weight, he, hn]

theorem weighted_mean_zero (d t : ℝ) :
    (∫ n, weight d t n * coordinate 2 n ∂angularMeasure) = 0 := by
  have h := integral_sphereMap (LinearIsometryEquiv.neg ℝ)
    (fun n => weight d t n * coordinate 2 n)
  simp only [weight_neg, coordinate_neg, mul_neg, integral_neg] at h
  linarith

def pole : Sphere := ⟨basis 2, by simp [basis, Sphere, mem_sphere, dist_zero_right]⟩

theorem coordinate_pole : coordinate 2 pole = 1 := by simp [coordinate, pole, basis]

theorem cap_positive (t : ℝ) (ht : t < 1) : 0 < angularMeasure (cap t) := by
  change 0 < (volume : Measure Space).toSphere (cap t)
  apply OQ14.SphereMeasure.volume_toSphere_open_pos _ (cap_open t)
  exact ⟨pole, by simpa [cap, coordinate_pole] using ht⟩

theorem weighted_denominator_positive (d t : ℝ) (hd : 0 ≤ d) :
    0 < ∫ n, weight d t n * coordinate 2 n ^ 2 ∂angularMeasure := by
  have hi := continuous_integrable _ ((coordinate_continuous 2).pow 2)
  have hp : 0 < ∫ n, coordinate 2 n ^ 2 ∂angularMeasure := by
    letI : Measure.IsOpenPosMeasure angularMeasure :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure Space).toSphere)
    exact integral_pos_of_integrable_nonneg_nonzero ((coordinate_continuous 2).pow 2) hi
      (fun _ => sq_nonneg _) (x := pole) (by simp [coordinate_pole])
  rw [weighted_integral _ _ _ ((coordinate_continuous 2).pow 2)]
  exact add_pos_of_pos_of_nonneg hp (mul_nonneg hd (integral_nonneg (fun _ => sq_nonneg _)))

theorem cap_balance_negative (t : ℝ) (ht0 : 0 ≤ t) (ht : t < 1)
    (htsq : 1 < 3 * t ^ 2) :
    (∫ n in cap t, (1 - 3 * coordinate 2 n ^ 2) ∂angularMeasure) < 0 := by
  let f : Sphere → ℝ := fun n => 3 * coordinate 2 n ^ 2 - 1
  have hc : Continuous f := (continuous_const.mul ((coordinate_continuous 2).pow 2)).sub continuous_const
  have hi := (continuous_integrable f hc).indicator (cap_open t).measurableSet
  have hpos (n : Sphere) (hn : n ∈ cap t) : 0 < f n := by
    have hn' : t < |coordinate 2 n| := hn
    have hs : t ^ 2 < coordinate 2 n ^ 2 := by nlinarith [sq_abs (coordinate 2 n)]
    dsimp [f]
    nlinarith
  have hnon : 0 ≤ (cap t).indicator f := by
    intro n
    by_cases hn : n ∈ cap t
    · simpa only [indicator_of_mem hn] using (hpos n hn).le
    · simp [hn]
  have hsupport : Function.support ((cap t).indicator f) = cap t := by
    ext n
    by_cases hn : n ∈ cap t
    · simp [Function.mem_support, hn, (hpos n hn).ne']
    · simp [hn]
  have hp : 0 < ∫ n, (cap t).indicator f n ∂angularMeasure :=
    (integral_pos_iff_support_of_nonneg hnon hi).mpr (by rw [hsupport]; exact cap_positive t ht)
  rw [integral_indicator (cap_open t).measurableSet] at hp
  have he : (fun n : Sphere => 1 - 3 * coordinate 2 n ^ 2) = -f := by funext n; dsimp [f]; ring
  rw [he]
  change (∫ n in cap t, -f n ∂angularMeasure) < 0
  rw [integral_neg]
  linarith

theorem coordinate_hasFDerivAt (i : Fin 3) (x : Space) :
    HasFDerivAt (fun y : Space => y i)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) x :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt

theorem tangentGradient_directional (i : Fin 3) (n : Sphere) (v : Space)
    (hv : ⟪(n : Space), v⟫_ℝ = 0) :
    ⟪tangentGradient i n, v⟫_ℝ =
      fderiv ℝ (fun y : Space => y i) (n : Space) v := by
  rw [(coordinate_hasFDerivAt i n).fderiv]
  simp [tangentGradient, basis, inner_sub_left, inner_smul_left,
    EuclideanSpace.inner_single_left, hv]

def numerator (d t : ℝ) : ℝ :=
  ∫ n, weight d t n * ‖tangentGradient 2 n‖ ^ 2 ∂angularMeasure
def denominator (d t : ℝ) : ℝ :=
  ∫ n, weight d t n * coordinate 2 n ^ 2 ∂angularMeasure
def quotient (d t : ℝ) : ℝ := numerator d t / denominator d t

theorem trial_balance (d t : ℝ) :
    numerator d t - 2 * denominator d t =
      d * ∫ n in cap t, (1 - 3 * coordinate 2 n ^ 2) ∂angularMeasure := by
  have h1 := weighted_integrable d t (fun n => 1 - coordinate 2 n ^ 2)
    (continuous_const.sub ((coordinate_continuous 2).pow 2))
  have h2 := weighted_integrable d t (fun n => coordinate 2 n ^ 2)
    ((coordinate_continuous 2).pow 2)
  have hb := weighted_integral d t (fun n => 1 - 3 * coordinate 2 n ^ 2)
    (continuous_const.sub (continuous_const.mul ((coordinate_continuous 2).pow 2)))
  rw [unweighted_balance 2, zero_add] at hb
  rw [← hb]
  unfold numerator denominator
  simp_rw [tangentGradient_norm_sq]
  rw [← integral_const_mul, ← integral_sub h1 (h2.const_mul 2)]
  apply integral_congr_ae
  filter_upwards with n
  ring

theorem quotient_lt_two_of_sq (d t : ℝ) (hd : 0 < d) (ht0 : 0 ≤ t)
    (ht : t < 1) (htsq : 1 < 3 * t ^ 2) : quotient d t < 2 := by
  have hp : 0 < denominator d t := weighted_denominator_positive d t hd.le
  have hn := mul_neg_of_pos_of_neg hd (cap_balance_negative t ht0 ht htsq)
  rw [← trial_balance] at hn
  unfold quotient
  apply (div_lt_iff₀ hp).mpr
  linarith

theorem quotient_lt_two (d t : ℝ) (hd : 0 < d)
    (ht : 1 / Real.sqrt 3 < t) (ht1 : t < 1) : quotient d t < 2 := by
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht0 : 0 < t := lt_trans (div_pos one_pos hp) ht
  have hs : (1 / Real.sqrt 3) ^ 2 = (1 / 3 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hsq := sq_lt_sq₀ (div_nonneg (by norm_num) hp.le) ht0.le |>.mpr ht
  rw [hs] at hsq
  exact quotient_lt_two_of_sq d t hd ht0.le ht1 (by linarith)

end OQ14.ConicalAngularTrial

#print axioms OQ14.ConicalAngularTrial.coordinate_continuous
#print axioms OQ14.ConicalAngularTrial.continuous_integrable
#print axioms OQ14.ConicalAngularTrial.coordinate_permutation
#print axioms OQ14.ConicalAngularTrial.square_integral_eq
#print axioms OQ14.ConicalAngularTrial.coordinate_squares
#print axioms OQ14.ConicalAngularTrial.unweighted_balance
#print axioms OQ14.ConicalAngularTrial.tangentGradient_inner
#print axioms OQ14.ConicalAngularTrial.tangentGradient_norm_sq
#print axioms OQ14.ConicalAngularTrial.cap_open
#print axioms OQ14.ConicalAngularTrial.weighted_integrable
#print axioms OQ14.ConicalAngularTrial.weighted_integral
#print axioms OQ14.ConicalAngularTrial.coordinate_neg
#print axioms OQ14.ConicalAngularTrial.weight_neg
#print axioms OQ14.ConicalAngularTrial.weighted_mean_zero
#print axioms OQ14.ConicalAngularTrial.coordinate_pole
#print axioms OQ14.ConicalAngularTrial.cap_positive
#print axioms OQ14.ConicalAngularTrial.weighted_denominator_positive
#print axioms OQ14.ConicalAngularTrial.cap_balance_negative
#print axioms OQ14.ConicalAngularTrial.coordinate_hasFDerivAt
#print axioms OQ14.ConicalAngularTrial.tangentGradient_directional
#print axioms OQ14.ConicalAngularTrial.trial_balance
#print axioms OQ14.ConicalAngularTrial.quotient_lt_two_of_sq
#print axioms OQ14.ConicalAngularTrial.quotient_lt_two
