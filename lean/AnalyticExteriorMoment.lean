import AnalyticOutgoingMode
import RealDyadicMomentOutgoing
import ComplexKernelRadialBasis
import ComplexResponseOverlap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.AnalyticExteriorMoment
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentOperator
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def sigma (p : Poly) : Sphere → ℂ := angularPolynomial p

theorem sigma_memLp (p : Poly) : MemLp (sigma p) 2 angularMeasure :=
  (angularPolynomial_continuous p).memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

def momentVector (n : ℝ) (hn : 1 < n) (T a b : ℝ) (u : VectorL2)
    (p : Poly) (i : Fin 3) (z : ℂ) : RadialL2 :=
  RadialFiniteSpan.cutOperator (Icc a b) measurableSet_Icc
    (operator (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p)
      (DynamicConvolution.component i (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u)))

theorem momentVector_analytic (n : ℝ) (hn : 1 < n) (T a b : ℝ) (hT : 0 ≤ T+1)
    (u : VectorL2) (p : Poly) (i : Fin 3) (z : ℂ) : AnalyticAt ℂ (momentVector n hn T a b u p i) z := by
  have h := (ComplexExteriorResponse.response_differentiable (ModalWeightedMode.coefficient n hn) 1 T hT u).analyticAt z
  exact ((RadialFiniteSpan.cutOperator (Icc a b) measurableSet_Icc).analyticAt _).comp
    (((operator (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p)).analyticAt _).comp
      (((DynamicConvolution.component i).analyticAt _).comp h))

theorem real_moment_ae (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 1 < a) (hb : b ≤ T)
    (u : VectorL2) (p : Poly) (i : Fin 3) (k : ℝ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      RadialMoment.moment (DynamicConvolution.component i
        (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) k 1 T u)) (sigma p) r =
      RadialMoment.moment (fun x => ComplexExteriorIntegral.field (ModalWeightedMode.coefficient n hn) k u x i) (sigma p) r := by
  let c := ModalWeightedMode.coefficient n hn
  let E := ComplexExteriorResponse.response c (k : ℂ) 1 T u
  have hlocal := ComplexExteriorIntegral.response_exterior_ae c k 1 T ((1+a)/2) (by linarith) u
    (ModalWeightedMode.coefficient_support n hn) i
  have hg : ∀ᵐ x : Space, x ∈ closedBall 0 T → ((1+a)/2 < ‖x‖ →
      (DynamicConvolution.component i E : Space → ℂ) x = ComplexExteriorIntegral.field c k u x i) := by
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hlocal,
      NewtonL2.physicalCoordinate_ae E i] with x hx hc hxT hxa
    exact hc.trans (hx hxT hxa)
  have hp := PolarMomentAE.polar_ae hg
  have hr : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Icc a b →
      RadialMoment.moment (DynamicConvolution.component i E) (sigma p) r =
      RadialMoment.moment (fun x => ComplexExteriorIntegral.field c k u x i) (sigma p) r := by
    filter_upwards [hp] with r hr hri
    have rpos : 0 < r := by linarith [hri.1]
    apply integral_congr_ae
    filter_upwards [hr] with ω hω
    have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos rpos]
    have hball : r • (ω : Space) ∈ closedBall (0 : Space) T := by
      simpa only [mem_closedBall, dist_zero_right, hnorm] using le_trans hri.2 hb
    have hrad : (1+a)/2 < ‖r • (ω : Space)‖ := by rw [hnorm]; linarith [hri.1]
    rw [hω hball hrad]
  have hrestr := (ae_restrict_iff' measurableSet_Icc).mpr hr
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r h => by
    change 0 < r
    linarith [h.1]
  simpa only [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub] using hrestr

theorem real_moment_proportional (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 1 < a) (hb : b ≤ T)
    (u : VectorL2) (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0)
    (i : Fin 3) (k : ℝ) (hk : 0 < k) :
    ∃ d : ℂ, momentVector n hn T a b u p i k = d • AnalyticOutgoingMode.mode a b (by linarith) l k := by
  obtain ⟨A, hA⟩ := RealDyadicMomentOutgoing.outgoing_moment (ModalWeightedMode.coefficient n hn)
    k hk 1 (by norm_num) u (ModalWeightedMode.coefficient_support n hn) p l hp hh i
  refine ⟨A / (k : ℂ)^l, ?_⟩
  apply Lp.ext
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hM := real_moment_ae n hn T a b ha hb u p i k
  have hm := ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).mp hM)
    (s := Ioi (0 : ℝ))
  let E := ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) k 1 T u
  let P := operator (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p)
  filter_upwards [RadialFiniteSpan.cut_actual (Icc a b) measurableSet_Icc (P (DynamicConvolution.component i E)),
    operator_actual (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p) (DynamicConvolution.component i E),
    AnalyticOutgoingMode.mode_actual a b (by linarith) l k hk0,
    Lp.coeFn_smul (A / (k : ℂ)^l) (AnalyticOutgoingMode.mode a b (by linarith) l k), hm]
    with r hcut hP hout hsm hmoment
  change (RadialFiniteSpan.cut (Icc a b) measurableSet_Icc (P (DynamicConvolution.component i E))) r = _
  rw [hcut, hsm, Pi.smul_apply, hout]
  by_cases hr : r ∈ Icc a b
  · rw [indicator_of_mem hr, indicator_of_mem hr, hP]
    change (r : ℂ) * RadialMoment.moment (DynamicConvolution.component i E) (sigma p) r = _
    rw [hmoment hr]
    have hrad : 1 < r := lt_of_lt_of_le ha hr.1
    change (r : ℂ) * RadialMoment.moment (fun x => ComplexExteriorIntegral.field (ModalWeightedMode.coefficient n hn) k u x i) (angularPolynomial p) r = _
    rw [hA r hrad]
    simp only [smul_eq_mul]
    field_simp
    ring
  · simp [hr]

#print axioms OQ14.AnalyticExteriorMoment.real_moment_proportional
#print axioms OQ14.AnalyticExteriorMoment.momentVector_analytic
#print axioms OQ14.AnalyticExteriorMoment.real_moment_ae
end OQ14.AnalyticExteriorMoment





