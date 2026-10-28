import AnalyticExteriorMoment
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.AnalyticOutgoingSelection
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.PolarMomentOperator OQ14.AnalyticExteriorMoment OQ14.SphericalMomentEquation
open scoped Topology InnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

def determinant (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 0 < a) (u : VectorL2)
    (p : Poly) (l : ℕ) (i : Fin 3) (v w : RadialL2) (z : ℂ) : ℂ :=
  ⟪v, momentVector n hn T a b u p i z⟫_ℂ * ⟪w, AnalyticOutgoingMode.mode a b ha l z⟫_ℂ -
  ⟪w, momentVector n hn T a b u p i z⟫_ℂ * ⟪v, AnalyticOutgoingMode.mode a b ha l z⟫_ℂ

theorem determinant_analytic (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 0 < a) (hT : 0 ≤ T+1)
    (u : VectorL2) (p : Poly) (l : ℕ) (i : Fin 3) (v w : RadialL2) (z : ℂ) :
    AnalyticAt ℂ (determinant n hn T a b ha u p l i v w) z := by
  have hm := momentVector_analytic n hn T a b hT u p i z
  have ho := AnalyticOutgoingMode.mode_analytic a b ha l z
  unfold determinant
  exact (((innerSL ℂ v).analyticAt _).comp hm |>.mul (((innerSL ℂ w).analyticAt _).comp ho)).sub
    ((((innerSL ℂ w).analyticAt _).comp hm).mul (((innerSL ℂ v).analyticAt _).comp ho))

theorem determinant_zero (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ T)
    (u : VectorL2) (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0)
    (i : Fin 3) (v w : RadialL2) (z : ℂ) :
    determinant n hn T a b (by linarith) u p l i v w z = 0 := by
  have hr (k : ℝ) (hk : 0 < k) : determinant n hn T a b (by linarith) u p l i v w k = 0 := by
    obtain ⟨d,hd⟩ := real_moment_proportional n hn T a b ha hb u p l hp hh i k hk
    unfold determinant
    rw [hd]
    simp only [inner_smul_right, smul_eq_mul]
    ring
  have hclosure : (1 : ℂ) ∈ closure ({z | determinant n hn T a b (by linarith) u p l i v w z = (0 : ℂ)} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1 + ε/2
    have hr0 : 0 < r := by dsimp [r]; linarith
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨hr r hr0, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ (determinant n hn T a b (by linarith) u p l i v w) Set.univ from
    fun q _ => determinant_analytic n hn T a b (by linarith) (by linarith) u p l i v w q).eqOn_of_preconnected_of_mem_closure
      (fun w _ => analyticAt_const) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem moment_proportional_of_mode_ne_zero (n : ℝ) (hn : 1 < n) (T a b : ℝ)
    (ha : 1 < a) (hab : a ≤ b) (hb : b ≤ T) (u : VectorL2) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0) (i : Fin 3) (z : ℂ)
    (hg : AnalyticOutgoingMode.mode a b (by linarith) l z ≠ 0) :
    ∃ d : ℂ, momentVector n hn T a b u p i z = d • AnalyticOutgoingMode.mode a b (by linarith) l z := by
  let G := AnalyticOutgoingMode.mode a b (by linarith) l z
  let M := momentVector n hn T a b u p i z
  have hG : G ≠ 0 := hg
  have hinner : ⟪G,G⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hG
  let d : ℂ := ⟪G,M⟫_ℂ / ⟪G,G⟫_ℂ
  have hz (w : RadialL2) : ⟪w, M - d • G⟫_ℂ = 0 := by
    have h := determinant_zero n hn T a b ha hab hb u p l hp hh i G w z
    change ⟪G,M⟫_ℂ * ⟪w,G⟫_ℂ - ⟪w,M⟫_ℂ * ⟪G,G⟫_ℂ = 0 at h
    rw [inner_sub_right, inner_smul_right]
    dsimp [d]
    field_simp [hinner]
    linear_combination -h
  have hzero : M - d • G = 0 := inner_self_eq_zero.mp (hz (M - d • G))
  exact ⟨d, sub_eq_zero.mp hzero⟩

theorem mode_ne_zero (a b : ℝ) (ha : 0 < a) (hab : a < b) (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    AnalyticOutgoingMode.mode a b ha l z ≠ 0 := by
  intro hzero
  have hzlp := Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  have hm := AnalyticOutgoingMode.mode_actual a b ha l z hz
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Icc a b →
      z^l * RadialRellich.outgoing l z r = 0 := by
    filter_upwards [hm,hzlp] with r hr hz0 hri
    rw [hzero, hz0, indicator_of_mem hri] at hr
    exact hr.symm
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun r h => by change 0 < r; linarith [h.1]
  have hae : (fun r => z^l * RadialRellich.outgoing l z r) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    have ht := ae_restrict_of_ae_restrict_of_subset hsub hpoint
    filter_upwards [ht, ae_restrict_mem measurableSet_Ioo] with r hr hri
    exact hr (Ioo_subset_Icc_self hri)
  have hcont : ContinuousOn (fun r => z^l * RadialRellich.outgoing l z r) (Ioo a b) := by
    intro r hr
    exact (continuousAt_const.mul ((RadialRellich.outgoing_hasDerivAt l z hz r
      (ne_of_gt (lt_trans ha hr.1))).continuousAt)).continuousWithinAt
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hcont continuous_const.continuousOn
  let r : ℝ := (a+b)/2
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans ha hr.1)
  have hfun : RadialRellich.outgoing l z =ᶠ[𝓝 r] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    have hv := heq ht
    exact (mul_eq_zero.mp hv).resolve_left (pow_ne_zero l hz)
  have hv : RadialRellich.outgoing l z r = 0 := hfun.eq_of_nhds
  have hd : RadialRellich.outgoingD l z r = 0 := by
    have he := hfun.deriv_eq
    have ho := (RadialRellich.outgoing_hasDerivAt l z hz r hr0).deriv
    simpa only [ho, deriv_zero] using he
  have hw := RadialRellich.radial_wronskian l z hz r hr0
  rw [hv, hd] at hw
  have hcontr : (-2 : ℂ) * I * z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz
  exact hcontr (by simpa using hw.symm)

theorem outgoing_moment (n : ℝ) (hn : 1 < n) (T a b : ℝ) (ha : 1 < a) (hab : a < b) (hb : b ≤ T)
    (u : VectorL2) (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0)
    (i : Fin 3) (z : ℂ) (hz : z ≠ 0) :
    ∃ d : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)
        (angularPolynomial p) r = d * RadialRellich.outgoing l z r := by
  have ha0 : 0 < a := by linarith
  obtain ⟨d,hd⟩ := moment_proportional_of_mode_ne_zero n hn T a b ha hab.le hb u p l hp hh i z
    (mode_ne_zero a b ha0 hab l z hz)
  refine ⟨d * z^l, ?_⟩
  let E := ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
  let P := operator (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p)
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Icc a b →
      (r : ℂ) * RadialMoment.moment (NewtonL2.physicalCoordinate E i) (angularPolynomial p) r =
        (d*z^l) * RadialRellich.outgoing l z r := by
    filter_upwards [RadialFiniteSpan.cut_actual (Icc a b) measurableSet_Icc (P (DynamicConvolution.component i E)),
      operator_actual (sigma p) (angularPolynomial_continuous p).measurable (sigma_memLp p) (DynamicConvolution.component i E),
      AnalyticOutgoingMode.mode_actual a b ha0 l z hz,
      Lp.coeFn_smul d (AnalyticOutgoingMode.mode a b ha0 l z)] with r hcut hP hout hsm hr
    have he := congrArg (fun x : RadialL2 => x r) hd
    change (RadialFiniteSpan.cut (Icc a b) measurableSet_Icc (P (DynamicConvolution.component i E))) r =
      (d • AnalyticOutgoingMode.mode a b ha0 l z) r at he
    rw [hcut, hsm, Pi.smul_apply, hout, indicator_of_mem hr, indicator_of_mem hr, hP] at he
    change (r : ℂ) * RadialMoment.moment (NewtonL2.physicalCoordinate E i) (angularPolynomial p) r = _ at he
    simpa only [smul_eq_mul, mul_assoc] using he
  have hrestr := (ae_restrict_iff' measurableSet_Icc).mpr hpoint
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => by change 0 < r; linarith [hr.1]
  simpa only [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub] using hrestr

#print axioms OQ14.AnalyticOutgoingSelection.outgoing_moment
#print axioms OQ14.AnalyticOutgoingSelection.mode_ne_zero
#print axioms OQ14.AnalyticOutgoingSelection.moment_proportional_of_mode_ne_zero
#print axioms OQ14.AnalyticOutgoingSelection.determinant_analytic
#print axioms OQ14.AnalyticOutgoingSelection.determinant_zero
end OQ14.AnalyticOutgoingSelection





