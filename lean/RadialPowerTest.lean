import WeakPoynting.Conservation
import FarFieldPower
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Actual real compact C1 radial tests and their gradient pairing with the real
Poynting vector. All derivatives are the genuine Euclidean Frechet derivatives.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.RadialPowerTest
open MeasureTheory Metric OQ14.Maxwell OQ14.WeakConservation OQ14.FarFieldPower
open scoped InnerProductSpace ComplexConjugate Topology

def radial (θ : ℝ → ℝ) (x : Space) : ℝ := θ (‖x‖^2)

theorem radial_regular (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) :
    ContDiff ℝ 1 (radial θ) := hθ.comp (contDiff_norm_sq ℝ)

theorem radial_partial (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (x : Space) (i : Fin 3) :
    fderiv ℝ (radial θ) x (basis i) = 2 * deriv θ (‖x‖^2) * x i := by
  have hd := (hθ.differentiable (by norm_num) (‖x‖^2)).hasDerivAt.comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hv := congrArg (fun L : Space →L[ℝ] ℝ => L (basis i)) hd.fderiv
  simpa [radial, ContinuousLinearMap.comp_apply, basis, EuclideanSpace.inner_single_right,
    mul_comm, mul_left_comm, mul_assoc] using hv

theorem radial_tsupport_subset (θ : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ q, R^2 ≤ q → θ q = 0) :
    tsupport (radial θ) ⊆ closedBall (0 : Space) R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hn : ‖x‖ ≤ R := by
    by_contra h
    have hr : R < ‖x‖ := lt_of_not_ge h
    have hs : R^2 ≤ ‖x‖^2 := (sq_le_sq₀ hR (norm_nonneg _)).mpr hr.le
    exact hx (hz _ hs)
  simpa only [mem_closedBall, dist_zero_right] using hn

theorem radial_compact (θ : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ q, R^2 ≤ q → θ q = 0) : HasCompactSupport (radial θ) :=
  (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport (radial θ))
    (radial_tsupport_subset θ R hR hz)

def radialTest (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ q, R^2 ≤ q → θ q = 0) : RealTest (Set.univ : Set Space) where
  function := radial θ
  regular := radial_regular θ hθ
  compact := radial_compact θ R hR hz
  inside := Set.subset_univ _

theorem norm_mul_radialPower (E H : Field) (x : Space) :
    ‖x‖ * radialPower x (E x) (H x) =
      x 0 * realPower E H x 0 + x 1 * realPower E H x 1 + x 2 * realPower E H x 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold radialPower realPower dot MaxwellRadiation.direction GreenKernel.unitCoordinate
  simp only [Complex.add_re, Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_div, zero_mul, sub_zero]
  field_simp
  ring

theorem radial_testPower (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (R : ℝ) (hR : 0 ≤ R)
    (hz : ∀ q, R^2 ≤ q → θ q = 0) (E H : Field) (x : Space) :
    testPower (radialTest θ hθ R hR hz) E H x =
      2 * deriv θ (‖x‖^2) * ‖x‖ * radialPower x (E x) (H x) := by
  change fderiv ℝ (radial θ) x (basis 0) * realPower E H x 0 +
    fderiv ℝ (radial θ) x (basis 1) * realPower E H x 1 +
    fderiv ℝ (radial θ) x (basis 2) * realPower E H x 2 = _
  rw [radial_partial θ hθ, radial_partial θ hθ, radial_partial θ hθ]
  rw [mul_assoc (2 * deriv θ (‖x‖^2)) ‖x‖, norm_mul_radialPower]
  ring

def betaBump : ContDiffBump (2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def beta (q : ℝ) : ℝ := betaBump q

theorem beta_regular : ContDiff ℝ 1 beta := betaBump.contDiff

theorem beta_nonnegative (q : ℝ) : 0 ≤ beta q := betaBump.nonneg

theorem beta_two : beta 2 = 1 := by
  apply betaBump.one_of_mem_closedBall
  simp [betaBump]

theorem beta_zero_left (q : ℝ) (hq : q ≤ 1) : beta q = 0 := by
  apply betaBump.zero_of_le_dist
  change 1 ≤ dist q 2
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem beta_zero_right (q : ℝ) (hq : 3 ≤ q) : beta q = 0 := by
  apply betaBump.zero_of_le_dist
  change 1 ≤ dist q 2
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

def primitive (q : ℝ) : ℝ := ∫ t in q..4, beta t

theorem primitive_hasDerivAt (q : ℝ) : HasDerivAt primitive (-beta q) q :=
  intervalIntegral.integral_hasDerivAt_left
    (beta_regular.continuous.intervalIntegrable q 4)
    beta_regular.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    beta_regular.continuous.continuousAt

theorem primitive_deriv (q : ℝ) : deriv primitive q = -beta q :=
  (primitive_hasDerivAt q).deriv

theorem primitive_regular : ContDiff ℝ 1 primitive := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun q => (primitive_hasDerivAt q).differentiableAt
  · have he : deriv primitive = fun q => -beta q := funext primitive_deriv
    rw [he]
    exact beta_regular.continuous.neg

theorem primitive_zero_right (q : ℝ) (hq : 3 ≤ q) : primitive q = 0 := by
  unfold primitive
  calc
    _ = ∫ t in q..4, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact beta_zero_right t ((le_min hq (by norm_num)).trans ht.1)
    _ = 0 := by simp

theorem primitive_constant_left (q : ℝ) (hq : q ≤ 1) : primitive q = primitive 1 := by
  have hz : (∫ t in q..1, beta t) = 0 := by
    calc
      _ = ∫ t in q..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact beta_zero_left t (ht.2.trans (max_le hq le_rfl))
      _ = 0 := by simp
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (beta_regular.continuous.intervalIntegrable q 1)
    (beta_regular.continuous.intervalIntegrable 1 4)
  rw [hz, zero_add] at ha
  exact ha.symm

theorem primitive_one_positive : 0 < primitive 1 := by
  apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 4)
    beta_regular.continuous.continuousOn (fun t _ => beta_nonnegative t)
  exact ⟨2, by norm_num, by rw [beta_two]; norm_num⟩

def cutoff : RealTest (Set.univ : Set Space) :=
  radialTest primitive primitive_regular 2 (by norm_num)
    (fun q hq => primitive_zero_right q (by nlinarith))

theorem cutoff_constant_inner (x : Space) (hx : ‖x‖ ≤ 1) :
    cutoff.function x = primitive 1 := by
  apply primitive_constant_left
  nlinarith [norm_nonneg x]

theorem cutoff_zero_positive : 0 < cutoff.function 0 := by
  rw [cutoff_constant_inner 0 (by simp)]
  exact primitive_one_positive

theorem cutoff_testPower (E H : Field) (x : Space) :
    testPower cutoff E H x =
      -2 * beta (‖x‖^2) * ‖x‖ * radialPower x (E x) (H x) := by
  rw [cutoff, radial_testPower, primitive_deriv]
  ring

def radialTestOn (Ω : Set Space) (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ)
    (R : ℝ) (hR : 0 ≤ R) (hz : ∀ q, R^2 ≤ q → θ q = 0)
    (hΩ : closedBall (0 : Space) R ⊆ Ω) : RealTest Ω where
  function := radial θ
  regular := radial_regular θ hθ
  compact := radial_compact θ R hR hz
  inside := (radial_tsupport_subset θ R hR hz).trans hΩ

theorem radialTestOn_testPower (Ω : Set Space) (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ)
    (R : ℝ) (hR : 0 ≤ R) (hz : ∀ q, R^2 ≤ q → θ q = 0)
    (hΩ : closedBall (0 : Space) R ⊆ Ω) (E H : Field) (x : Space) :
    testPower (radialTestOn Ω θ hθ R hR hz hΩ) E H x =
      2 * deriv θ (‖x‖^2) * ‖x‖ * radialPower x (E x) (H x) :=
  radial_testPower θ hθ R hR hz E H x

def scaledPrimitive (a q : ℝ) : ℝ := primitive (q / a^2)

theorem scaledPrimitive_regular (a : ℝ) : ContDiff ℝ 1 (scaledPrimitive a) :=
  primitive_regular.comp (contDiff_id.div_const (a^2))

theorem scaledPrimitive_deriv (a q : ℝ) :
    deriv (scaledPrimitive a) q = -beta (q/a^2) / a^2 := by
  have hd := (primitive_hasDerivAt (q/a^2)).comp q ((hasDerivAt_id q).div_const (a^2))
  have he := hd.deriv
  change deriv (scaledPrimitive a) q = -beta (q/a^2) * (1/a^2) at he
  rw [he]
  ring

theorem scaledPrimitive_zero_right (a : ℝ) (ha : 0 < a) (q : ℝ)
    (hq : (2*a)^2 ≤ q) : scaledPrimitive a q = 0 := by
  apply primitive_zero_right
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith

def scaledCutoff (a : ℝ) (ha : 0 < a) : RealTest (Set.univ : Set Space) :=
  radialTest (scaledPrimitive a) (scaledPrimitive_regular a) (2*a) (by positivity)
    (scaledPrimitive_zero_right a ha)

theorem scaledCutoff_constant_inner (a : ℝ) (ha : 0 < a) (x : Space) (hx : ‖x‖ ≤ a) :
    (scaledCutoff a ha).function x = primitive 1 := by
  apply primitive_constant_left
  apply (div_le_one (sq_pos_of_pos ha)).mpr
  exact (sq_le_sq₀ (norm_nonneg x) ha.le).mpr hx

theorem scaledCutoff_zero_positive (a : ℝ) (ha : 0 < a) :
    0 < (scaledCutoff a ha).function 0 := by
  rw [scaledCutoff_constant_inner a ha 0 (by simpa using ha.le)]
  exact primitive_one_positive

theorem scaledCutoff_testPower (a : ℝ) (ha : 0 < a) (E H : Field) (x : Space) :
    testPower (scaledCutoff a ha) E H x =
      (-2/a^2) * beta (‖x‖^2/a^2) * ‖x‖ * radialPower x (E x) (H x) := by
  rw [scaledCutoff, radial_testPower, scaledPrimitive_deriv]
  ring

end OQ14.RadialPowerTest




#print axioms OQ14.RadialPowerTest.radial_regular
#print axioms OQ14.RadialPowerTest.radial_partial
#print axioms OQ14.RadialPowerTest.radial_tsupport_subset
#print axioms OQ14.RadialPowerTest.radial_compact
#print axioms OQ14.RadialPowerTest.norm_mul_radialPower
#print axioms OQ14.RadialPowerTest.radial_testPower
#print axioms OQ14.RadialPowerTest.beta_regular
#print axioms OQ14.RadialPowerTest.beta_nonnegative
#print axioms OQ14.RadialPowerTest.beta_two
#print axioms OQ14.RadialPowerTest.beta_zero_left
#print axioms OQ14.RadialPowerTest.beta_zero_right
#print axioms OQ14.RadialPowerTest.primitive_hasDerivAt
#print axioms OQ14.RadialPowerTest.primitive_deriv
#print axioms OQ14.RadialPowerTest.primitive_regular
#print axioms OQ14.RadialPowerTest.primitive_zero_right
#print axioms OQ14.RadialPowerTest.primitive_constant_left
#print axioms OQ14.RadialPowerTest.primitive_one_positive
#print axioms OQ14.RadialPowerTest.cutoff_constant_inner
#print axioms OQ14.RadialPowerTest.cutoff_zero_positive
#print axioms OQ14.RadialPowerTest.cutoff_testPower
#print axioms OQ14.RadialPowerTest.radialTestOn_testPower
#print axioms OQ14.RadialPowerTest.scaledPrimitive_regular
#print axioms OQ14.RadialPowerTest.scaledPrimitive_deriv
#print axioms OQ14.RadialPowerTest.scaledPrimitive_zero_right
#print axioms OQ14.RadialPowerTest.scaledCutoff_constant_inner
#print axioms OQ14.RadialPowerTest.scaledCutoff_zero_positive
#print axioms OQ14.RadialPowerTest.scaledCutoff_testPower
