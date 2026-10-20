import WeakPoynting.InteriorTestDensity

/-! # Compact smooth identities imply the genuine regional weak curl -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.RegionalCurlUpgrade

open MeasureTheory OQ14.Maxwell OQ14.WeakGreen OQ14.PartialSmoothing
  OQ14.InteriorTestDensity OQ14.CurlCutoff Filter
open scoped Topology SchwartzMap

theorem extended_pair_schwartz {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (u : DomainCurl.L2Scalar Ω) (f : 𝓢(Space, ℂ)) (hc : HasCompactSupport (f : Space → ℂ)) :
    scalarProduct (extendScalar Ω hΩ u) (FourierL2.embed f) =
      ∫ x in Ω, u x * f x := by
  rw [scalarProduct_embed]
  rw [← WeakCurl.testPair_integral (f : Space → ℂ) f.continuous hc]
  rw [extendScalar_pair, DomainCurl.testPair_integral]

/-- Smooth test identities are sufficient for the actual compact C1 definition
of the regional weak curl. The fields are only L2 on Ω. -/
theorem hasWeakCurl_of_schwartz_integrals {Ω : Set Space} (hΩ : IsOpen Ω)
    (E C : DomainCurl.L2Vector Ω)
    (h : ∀ f : 𝓢(Space, ℂ), HasCompactSupport (f : Space → ℂ) →
      tsupport (f : Space → ℂ) ⊆ Ω → ∀ j : Fin 3,
      (∫ x in Ω, C j x * f x) =
        (∫ x in Ω, E (WeakCurl.next j) x * dcoord f x (WeakCurl.previous j)) -
        (∫ x in Ω, E (WeakCurl.previous j) x * dcoord f x (WeakCurl.next j))) :
    DomainCurl.HasWeakCurl Ω E C := by
  apply (DomainCurl.hasWeakCurl_iff_integral Ω E C).mpr
  intro φ j
  obtain ⟨K, f, hK, hKΩ, hs, hf, hd⟩ := interior_test_approximation hΩ φ
  have hc (n : ℕ) : HasCompactSupport (f n : Space → ℂ) :=
    hK.of_isClosed_subset isClosed_closure (hs n)
  have hl := (scalarProduct (extendScalar Ω hΩ.measurableSet (C j))).continuous.tendsto _ |>.comp hf
  have hr := ((scalarProduct (extendScalar Ω hΩ.measurableSet (E (WeakCurl.next j)))).continuous.tendsto _
      |>.comp (hd (WeakCurl.previous j))).sub
    ((scalarProduct (extendScalar Ω hΩ.measurableSet (E (WeakCurl.previous j)))).continuous.tendsto _
      |>.comp (hd (WeakCurl.next j)))
  have he (n : ℕ) :
      scalarProduct (extendScalar Ω hΩ.measurableSet (C j)) (FourierL2.embed (f n)) =
        scalarProduct (extendScalar Ω hΩ.measurableSet (E (WeakCurl.next j)))
          (FourierL2.embed (GradientProjection.pderivative (WeakCurl.previous j) (f n))) -
        scalarProduct (extendScalar Ω hΩ.measurableSet (E (WeakCurl.previous j)))
          (FourierL2.embed (GradientProjection.pderivative (WeakCurl.next j) (f n))) := by
    rw [extended_pair_schwartz hΩ.measurableSet (C j) (f n) (hc n),
      extended_pair_schwartz hΩ.measurableSet (E (WeakCurl.next j))
        (GradientProjection.pderivative (WeakCurl.previous j) (f n))
        ((hc n).fderiv_apply ℝ (basis (WeakCurl.previous j))),
      extended_pair_schwartz hΩ.measurableSet (E (WeakCurl.previous j))
        (GradientProjection.pderivative (WeakCurl.next j) (f n))
        ((hc n).fderiv_apply ℝ (basis (WeakCurl.next j)))]
    simpa only [GradientProjection.pderivative_apply] using h (f n) (hc n) ((hs n).trans hKΩ) j
  have heq := tendsto_nhds_unique hl
    (hr.congr' (Eventually.of_forall (fun n => (he n).symm)))
  simpa only [testL2, testDerivativeL2, scalarProduct_continuousL2,
    extendScalar_pair, DomainCurl.testPair_integral] using heq

theorem hasWeakCurl_of_smooth_integrals {Ω : Set Space} (hΩ : IsOpen Ω)
    (E C : DomainCurl.L2Vector Ω)
    (h : ∀ f : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ Ω → ∀ j : Fin 3,
      (∫ x in Ω, C j x * f x) =
        (∫ x in Ω, E (WeakCurl.next j) x * dcoord f x (WeakCurl.previous j)) -
        (∫ x in Ω, E (WeakCurl.previous j) x * dcoord f x (WeakCurl.next j))) :
    DomainCurl.HasWeakCurl Ω E C := by
  apply hasWeakCurl_of_schwartz_integrals hΩ E C
  intro f hc hi j
  exact h f (f.smooth (⊤ : ℕ∞)) hc hi j

/-- Actual locally square-integrable coordinate fields satisfying global
compact smooth test identities produce genuine regional H(curl) data. -/
theorem fields_hasWeakCurl_of_global_smooth {Ω : Set Space} (hΩ : IsOpen Ω)
    (E C : Field)
    (hE : ∀ j, MemLp (fun x => E x j) 2 (DomainCurl.regionMeasure Ω))
    (hC : ∀ j, MemLp (fun x => C x j) 2 (DomainCurl.regionMeasure Ω))
    (h : ∀ f : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ Ω → ∀ j : Fin 3,
      (∫ x, C x j * f x) =
        (∫ x, E x (WeakCurl.next j) * dcoord f x (WeakCurl.previous j)) -
        (∫ x, E x (WeakCurl.previous j) * dcoord f x (WeakCurl.next j))) :
    DomainCurl.HasWeakCurl Ω (DomainCurl.fieldToL2 Ω E hE) (DomainCurl.fieldToL2 Ω C hC) := by
  apply hasWeakCurl_of_smooth_integrals hΩ
  intro f hf hc hi j
  simp only [DomainCurl.fieldToL2_integral]
  let φ : DomainCurl.Test Ω :=
    ⟨⟨f, hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1), hc⟩, hi⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [show f x = 0 from DomainCurl.test_zero_outside Ω φ hx, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [show dcoord f x (WeakCurl.previous j) = 0 from
        DomainCurl.derivative_test_zero_outside Ω φ (WeakCurl.previous j) hx, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [show dcoord f x (WeakCurl.next j) = 0 from
        DomainCurl.derivative_test_zero_outside Ω φ (WeakCurl.next j) hx, mul_zero])]
  exact h f hf hc hi j

end OQ14.RegionalCurlUpgrade

#print axioms OQ14.RegionalCurlUpgrade.extended_pair_schwartz
#print axioms OQ14.RegionalCurlUpgrade.hasWeakCurl_of_schwartz_integrals
#print axioms OQ14.RegionalCurlUpgrade.hasWeakCurl_of_smooth_integrals
#print axioms OQ14.RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth
