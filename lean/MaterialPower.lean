import MaterialHCurl

/-! # Actual local power conservation for the constructed dielectric fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.MaterialPower

open MeasureTheory Metric OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MaterialHCurl
  OQ14.WeakConservation

def powerPair (χ : Space → ℝ) (E H : Field) (x : Space) : ℝ :=
  fderiv ℝ χ x (basis 0) * realPower E H x 0 +
  fderiv ℝ χ x (basis 1) * realPower E H x 1 +
  fderiv ℝ χ x (basis 2) * realPower E H x 2

theorem regional_power {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (k : ℝ) (ε : Space → ℝ) (E H : Field)
    (hE : ∀ j, MemLp (fun x => E x j) 2 (DomainCurl.regionMeasure Ω))
    (hH : ∀ j, MemLp (fun x => H x j) 2 (DomainCurl.regionMeasure Ω))
    (hD : ∀ j, MemLp (fun x => (ε x : ℂ) * E x j) 2 (DomainCurl.regionMeasure Ω))
    (hMax : TestMaxwell k ε E H) :
    Integrable (powerPair χ.function E H) (DomainCurl.regionMeasure Ω) ∧
      (∫ x in Ω, powerPair χ.function E H x) = 0 := by
  obtain ⟨e, h, he, hh, hM⟩ := exists_regional_fields hΩ k ε E H hE hH hD hMax
  have heq : testPower χ (fun x j => e.val.1 j x) (fun x j => h.val.1 j x)
      =ᵐ[DomainCurl.regionMeasure Ω] powerPair χ.function E H := by
    filter_upwards [ae_all_iff.mpr he, ae_all_iff.mpr hh] with x hx hy
    have hx' : (fun j => e.val.1 j x) = E x := funext hx
    have hy' : (fun j => h.val.1 j x) = H x := funext hy
    simp only [testPower, powerPair, realPower, hx', hy']
  exact ⟨(weak_real_power_integrable hΩ χ k (fun _ => 1) ε e h hM).congr heq,
    (integral_congr_ae heq).symm.trans
      (weak_real_power_conservation hΩ χ k (fun _ => 1) ε e h hM)⟩

theorem powerPair_zero_outside (χ : Space → ℝ) (E H : Field)
    (x : Space) (hx : x ∉ tsupport χ) : powerPair χ E H x = 0 := by
  simp only [powerPair, fderiv_of_not_mem_tsupport ℝ hx,
    ContinuousLinearMap.zero_apply, zero_mul, add_zero]

/-- The physical Poynting pairing of the actual spatial fields is globally
integrable and vanishes for every real compact C1 test. -/
theorem testMaxwell_power (k : ℝ) (ε : Space → ℝ)
    (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k ε E H)
    (χ : Space → ℝ) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) :
    Integrable (powerPair χ E H) volume ∧ (∫ x, powerPair χ E H x) = 0 := by
  obtain ⟨T, hT⟩ := hcχ.isBounded.subset_ball (0 : Space)
  let φ : RealTest (ball (0 : Space) T) := ⟨χ, hχ, hcχ, hT⟩
  have hEΩ := fun j => memLp_bounded_of_balls _ (fun S => hE S j) (ball 0 T) isBounded_ball
  have hHΩ := fun j => memLp_bounded_of_balls _ (fun S => hH S j) (ball 0 T) isBounded_ball
  obtain ⟨hi, hz⟩ := regional_power isOpen_ball φ k ε E H hEΩ hHΩ
    (fun j => coefficient_mul_memLp _ ε hε M hb _ (hEΩ j)) hMax
  have hout : ∀ x, x ∉ ball (0 : Space) T → powerPair χ E H x = 0 :=
    fun x hx => powerPair_zero_outside χ E H x (fun hs => hx (hT hs))
  have he : (ball (0 : Space) T).indicator (powerPair χ E H) = powerPair χ E H := by
    funext x
    by_cases hx : x ∈ ball (0 : Space) T
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_not_mem hx, hout x hx]
  constructor
  · rw [← he]
    exact (integrable_indicator_iff measurableSet_ball).mpr hi
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hz
    exact hz

/-- Local real power conservation follows for the actual volume-solution
fields; it is not imposed on the incident-plus-scattered construction. -/
theorem small_volume_power_exists (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (hR : 0 ≤ R) (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorFourier.VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      ∀ χ : Space → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
        Integrable (powerPair χ (MaterialField.total c k u Einc) (totalMagnetic c k u Hinc)) volume ∧
        (∫ x, powerPair χ (MaterialField.total c k u Einc) (totalMagnetic c k u Hinc) x) = 0 := by
  obtain ⟨u, hu, _, hM, hEu, hHu⟩ :=
    SmallVolumeMaxwell.exists_small_volume_fields c k R hR hsmall hc Einc Hinc hE hH hMax
  refine ⟨u, hu, ?_⟩
  intro χ hχ hcχ
  exact testMaxwell_power k (dielectric c) (dielectric_measurable c) (1+c.bound)
    (dielectric_norm_bound c) _ _ hEu hHu hM χ hχ hcχ

end OQ14.MaterialPower

#print axioms OQ14.MaterialPower.regional_power
#print axioms OQ14.MaterialPower.powerPair_zero_outside
#print axioms OQ14.MaterialPower.testMaxwell_power
#print axioms OQ14.MaterialPower.small_volume_power_exists
