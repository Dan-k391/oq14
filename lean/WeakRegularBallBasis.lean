import RegularBallMoments
import AnnularMollifierBasis
import RadialFiniteSpan

/-! Regular radial modes for the actual weak L2 field on a ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.WeakRegularBallBasis
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.WeakPoynting
  OQ14.PolarMomentOperator OQ14.RadialFiniteSpan OQ14.RadialOriginSelection
open scoped Topology

theorem eventually_regular_moment (L b : ℝ) (hb : 0 < b) (hbL : b < L)
    (k : ℂ) (hk : k ≠ 0) (u : PolarMomentEnergy.ScalarL2)
    (hw : WeakHelmholtzRegularity.IsWeakHelmholtz k (ball 0 L) u)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ᶠ n : ℕ in atTop, ∃ c : ℂ, ∀ r ∈ Ioo 0 b,
      (r : ℂ) * RadialMoment.moment (smoothScalar (complexKernel (shrinkingBump n)) u)
        (SphericalMomentEquation.angularPolynomial p) r = c * regular l k r := by
  filter_upwards [HelmholtzMollifiers.eventually_helmholtz_on_fixed_ball k 0 L b hbL u
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hw] with n hn
  exact RegularBallMoments.regular_moment b hb k hk _
    (smoothScalar_regular (complexKernel_regular _) (complexKernel_compact _) u) hn p l hp hh

theorem moment_expansion (L a b : ℝ) (ha : 0 < a) (hbL : b < L) (hL : 0 < L)
    (k : ℂ) (hk : k ≠ 0) (u : PolarMomentEnergy.ScalarL2)
    (hw : WeakHelmholtzRegularity.IsWeakHelmholtz k (ball 0 L) u)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment u (SphericalMomentEquation.angularPolynomial p) r =
        c * regular l k r := by
  let σ := SphericalMomentEquation.angularPolynomial p
  have hσc : Continuous σ := SphericalMomentEquation.angularPolynomial_continuous p
  have hσm : Measurable σ := hσc.measurable
  have hσ : MemLp σ 2 angularMeasure := hσc.memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hv : ContinuousOn (regular l k) (Icc a b) := fun r _ =>
    (regular_hasDerivAt l k r).continuousAt.continuousWithinAt
  let v := compactMode a b (regular l k) hv
  let C := cutOperator (Icc a b) measurableSet_Icc
  let P := operator σ hσm hσ
  let F : ℕ → RadialL2 := fun n => C (P (mollifyL2 (shrinkingBump n) u))
  let g := C (P u)
  have hlim : Tendsto F atTop (𝓝 g) := C.continuous.continuousAt.tendsto.comp
    (AnnularMollifierBasis.radial_mollifiers_tendsto σ hσm hσ u)
  let B := (max b 0 + L)/2
  have hBL : B < L := by
    have hm : max b 0 < L := max_lt hbL hL
    dsimp [B]
    linarith
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right b 0]
  have hbB : b < B := by dsimp [B]; linarith [le_max_left b 0]
  have hevent := eventually_regular_moment L B hB hBL k hk u hw p l hp hh
  let S := Submodule.span ℂ ({v} : Set RadialL2)
  have hmem : ∀ᶠ n : ℕ in atTop, F n ∈ S := by
    filter_upwards [hevent] with n hn
    obtain ⟨c,hc⟩ := hn
    have heq : F n = c • v := by
      apply Lp.ext
      filter_upwards [cut_actual (Icc a b) measurableSet_Icc (P (mollifyL2 (shrinkingBump n) u)),
        AnnularMollifierBasis.radial_mollifier_actual σ hσm hσ u n,
        compactMode_actual a b (regular l k) hv, Lp.coeFn_smul c v]
        with r hcut hrad hvv hcv
      change (cut (Icc a b) measurableSet_Icc (P (mollifyL2 (shrinkingBump n) u))) r = _
      rw [hcut, hcv, Pi.smul_apply]
      change (Icc a b).indicator (P (mollifyL2 (shrinkingBump n) u)) r =
        c * compactMode a b (regular l k) hv r
      rw [hvv]
      by_cases hr : r ∈ Icc a b
      · rw [indicator_of_mem hr, indicator_of_mem hr]
        change (operator σ hσm hσ (mollifyL2 (shrinkingBump n) u)) r = _
        rw [hrad]
        exact hc r ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hbB⟩
      · simp only [indicator_of_not_mem hr, mul_zero]
    rw [heq]
    exact S.smul_mem c (Submodule.subset_span (by simp))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hg : g ∈ S := S.closed_of_finiteDimensional.mem_of_tendsto hlim hmem
  obtain ⟨c,heq⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨c,?_⟩
  have haeres : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Icc a b →
      (r : ℂ) * RadialMoment.moment u σ r = c * regular l k r := by
    filter_upwards [cut_actual (Icc a b) measurableSet_Icc (P u), operator_actual σ hσm hσ u,
      compactMode_actual a b (regular l k) hv, Lp.coeFn_smul c v]
      with r hcut hrad hvv hcv hr
    have h := congrArg (fun f : RadialL2 => f r) heq
    change (c • v) r = cut (Icc a b) measurableSet_Icc (P u) r at h
    rw [hcv, Pi.smul_apply, hcut] at h
    change c * compactMode a b (regular l k) hv r = (Icc a b).indicator (P u) r at h
    rw [hvv, indicator_of_mem hr, indicator_of_mem hr] at h
    change _ = (operator σ hσm hσ u) r at h
    rw [hrad] at h
    exact h.symm
  have hrestr := (ae_restrict_iff' measurableSet_Icc).mpr haeres
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le ha hr.1
  simpa only [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub] using hrestr

end OQ14.WeakRegularBallBasis
#print axioms OQ14.WeakRegularBallBasis.eventually_regular_moment
#print axioms OQ14.WeakRegularBallBasis.moment_expansion
