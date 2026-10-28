import AnnularMollifierBasis
import RadialFiniteSpan

/-! Two actual Riccati modes for arbitrary L2 weak Helmholtz moments on compact annuli. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.WeakAnnularBasis
open MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.WeakPoynting
  OQ14.PolarMomentOperator OQ14.RadialFiniteSpan OQ14.RadialRellich
open scoped Topology

theorem moment_expansion (R L a b : ℝ) (hR : 0 ≤ R) (hRa : R < a) (hbL : b < L)
    (k : ℂ) (hk : k ≠ 0) (u : PolarMomentEnergy.ScalarL2)
    (hw : WeakHelmholtzRegularity.IsWeakHelmholtz k (AnnularMoment.annulus R L) u)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c d : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment u (SphericalMomentEquation.angularPolynomial p) r =
        c * outgoing l k r + d * incoming l k r := by
  let σ := SphericalMomentEquation.angularPolynomial p
  have hσc : Continuous σ := SphericalMomentEquation.angularPolynomial_continuous p
  have hσm : Measurable σ := hσc.measurable
  have hσ : MemLp σ 2 angularMeasure := hσc.memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have ha0 : 0 < a := lt_of_le_of_lt hR hRa
  have hv : ContinuousOn (outgoing l k) (Icc a b) := fun r hr =>
    (outgoing_hasDerivAt l k hk r (ne_of_gt (lt_of_lt_of_le ha0 hr.1))).continuousAt.continuousWithinAt
  have hwc : ContinuousOn (incoming l k) (Icc a b) := fun r hr =>
    (incoming_hasDerivAt l k hk r (ne_of_gt (lt_of_lt_of_le ha0 hr.1))).continuousAt.continuousWithinAt
  let v := compactMode a b (outgoing l k) hv
  let w := compactMode a b (incoming l k) hwc
  let C := cutOperator (Icc a b) measurableSet_Icc
  let P := operator σ hσm hσ
  let F : ℕ → RadialL2 := fun n => C (P (mollifyL2 (shrinkingBump n) u))
  let g := C (P u)
  have hlim : Tendsto F atTop (𝓝 g) := C.continuous.continuousAt.tendsto.comp
    (AnnularMollifierBasis.radial_mollifiers_tendsto σ hσm hσ u)
  have hevent := AnnularMollifierBasis.eventually_moment_expansion R L ((R+a)/2) ((b+L)/2)
    (by linarith) (by linarith) (by linarith) k hk u hw p l hp hh
  have hmem : ∀ᶠ n : ℕ in atTop, F n ∈ Submodule.span ℂ ({v,w} : Set RadialL2) := by
    filter_upwards [hevent] with n hn
    obtain ⟨c,d,hcd⟩ := hn
    have heq : F n = c • v + d • w := by
      apply Lp.ext
      filter_upwards [cut_actual (Icc a b) measurableSet_Icc (P (mollifyL2 (shrinkingBump n) u)),
        AnnularMollifierBasis.radial_mollifier_actual σ hσm hσ u n,
        compactMode_actual a b (outgoing l k) hv, compactMode_actual a b (incoming l k) hwc,
        Lp.coeFn_add (c • v) (d • w), Lp.coeFn_smul c v, Lp.coeFn_smul d w]
        with r hcut hrad hvv hww hadd hcv hdw
      change (cut (Icc a b) measurableSet_Icc (P (mollifyL2 (shrinkingBump n) u))) r = _
      rw [hcut, hadd, Pi.add_apply, hcv, hdw, Pi.smul_apply, Pi.smul_apply]
      change (Icc a b).indicator (P (mollifyL2 (shrinkingBump n) u)) r =
        c * compactMode a b (outgoing l k) hv r + d * compactMode a b (incoming l k) hwc r
      rw [hvv,hww]
      by_cases hr : r ∈ Icc a b
      · rw [indicator_of_mem hr, indicator_of_mem hr, indicator_of_mem hr]
        change (operator σ hσm hσ (mollifyL2 (shrinkingBump n) u)) r = _
        rw [hrad]
        exact hcd r ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · simp only [indicator_of_not_mem hr, mul_zero, add_zero]
    rw [heq]
    exact (Submodule.span ℂ ({v,w} : Set RadialL2)).add_mem
      ((Submodule.span ℂ ({v,w} : Set RadialL2)).smul_mem c (Submodule.subset_span (by simp)))
      ((Submodule.span ℂ ({v,w} : Set RadialL2)).smul_mem d (Submodule.subset_span (by simp)))
  obtain ⟨c,d,heq⟩ := Submodule.mem_span_pair.mp (limit_in_two_mode_span v w F g hlim hmem)
  refine ⟨c,d,?_⟩
  have haeres : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Icc a b →
      (r : ℂ) * RadialMoment.moment u σ r = c * outgoing l k r + d * incoming l k r := by
    filter_upwards [cut_actual (Icc a b) measurableSet_Icc (P u), operator_actual σ hσm hσ u,
      compactMode_actual a b (outgoing l k) hv, compactMode_actual a b (incoming l k) hwc,
      Lp.coeFn_add (c • v) (d • w), Lp.coeFn_smul c v, Lp.coeFn_smul d w]
      with r hcut hrad hvv hww hadd hcv hdw hr
    have h := congrArg (fun f : RadialL2 => f r) heq
    change (c • v + d • w) r = cut (Icc a b) measurableSet_Icc (P u) r at h
    rw [hadd, Pi.add_apply, hcv, hdw, Pi.smul_apply, Pi.smul_apply, hcut] at h
    change c * compactMode a b (outgoing l k) hv r + d * compactMode a b (incoming l k) hwc r =
      (Icc a b).indicator (P u) r at h
    rw [hvv,hww,indicator_of_mem hr,indicator_of_mem hr,indicator_of_mem hr] at h
    change _ = (operator σ hσm hσ u) r at h
    rw [hrad] at h
    exact h.symm
  have hrestr := (ae_restrict_iff' measurableSet_Icc).mpr haeres
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le ha0 hr.1
  simpa only [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub] using hrestr

end OQ14.WeakAnnularBasis
#print axioms OQ14.WeakAnnularBasis.moment_expansion
