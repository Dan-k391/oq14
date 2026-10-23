import ConicalInputCoefficient

/-! Select one literal finite Maxwell incident field with a nonzero conical coefficient before rounding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalFixedFiniteInput
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space

theorem exists_nonzero_numerator (p : Data) (a b R k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : 0 < k)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R)
    (hne : ConicalCoefficientStability.numerator
      (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc≠0) :
    ∃ (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x),
      ConicalCoefficientStability.numerator
        (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ) ζ hζ hc≠0 := by
  obtain ⟨C,hC,hbound⟩ := ConicalInputCoefficient.numerator_error_bound p a b R k ha hai hba hRb hν hk.ne' hfreq ζ hζ hc hs
  let N := ConicalCoefficientStability.numerator
    (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc
  have hN : 0 < ‖N‖ := norm_pos_iff.mpr hne
  have hCp : 0 < C+1 := by linarith
  obtain ⟨c,hcapprox⟩ := ConicalSeparatedIllumination.finite_incident_approximation p a k ha hai hk
    (‖N‖/(2*(C+1))) (div_pos hN (by positivity))
  obtain ⟨J,hJ,hcomp,heJ⟩ := ConicalFiniteGauge.exists_incident_extension p a b k hai hba c
  refine ⟨c,J,hJ,heJ,?_⟩
  have hb := hbound c J (fun i => (hJ i).continuous) heJ
  have hl : C*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ < ‖N‖ := by
    calc
      _ ≤ (C+1)*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1)*(‖N‖/(2*(C+1))) := mul_lt_mul_of_pos_left hcapprox hCp
      _ = ‖N‖/2 := by field_simp; ring
      _ < ‖N‖ := by linarith
  intro hz
  rw [hz,zero_sub,norm_neg] at hb
  exact (not_lt_of_ge hb) hl

theorem exists_nonzero_coefficient (p : Data) (a b R k : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : 0 < k)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R)
    (hne : ConicalCoefficientStability.numerator
      (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc≠0) :
    ∃ (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
      (q : ℂ), q≠0 ∧
      ConicalGraphProjection.projected p
        (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ).graph
        =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
          q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
            (radialCorrection (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ))
            (tangentCorrection (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ)) r := by
  obtain ⟨c,J,hJ,heJ,hne⟩ := exists_nonzero_numerator p a b R k ha hai hba hRb hν hk hfreq ζ hζ hc hs hne
  let s := ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ
  obtain ⟨q,hq,he⟩ := ConicalLocalCoefficient.coefficient_identity s hb (hba.trans hai) hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hRb.le))
  refine ⟨c,J,hJ,heJ,q,?_,hq⟩
  intro hz
  rw [hz,mul_zero,zero_mul,zero_add] at he
  exact hne (sub_eq_zero.mpr he)


theorem eventually_nonzero_baseline (p : Data) (a R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hR : 0 < R) (hRa : R ≤ a) (hν : p.exponent < 1) :
    ∀ᶠ k : ℝ in 𝓝 0,
      ConicalSeparatedPairing.gradientPair p a k hai (ConicalSeparatedRetention.annularBump R hR)
        (ConicalSeparatedRetention.annularBump R hR).contDiff
        (ConicalSeparatedRetention.annularBump R hR).hasCompactSupport-
      ConicalSeparatedIdentity.particularPair p a k (ConicalSeparatedRetention.annularBump R hR)≠0 := by
  let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump R hR
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (ConicalSeparatedRetention.annularBump R hR).contDiff
  have hc : HasCompactSupport ζ := (ConicalSeparatedRetention.annularBump R hR).hasCompactSupport
  have hs := ConicalSeparatedRetention.annularBump_support R hR
  have hne := ConicalStaticCoefficient.static_pairing_ne_zero p hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right (hRa.trans hai.le)))
    (fun r => (ConicalSeparatedRetention.annularBump R hR).nonneg)
    (R/2) (by linarith) (by
      have h : ζ (R/2)=1 := (ConicalSeparatedRetention.annularBump R hR).one_of_mem_closedBall (by
        simp only [mem_closedBall,dist_self]; exact (ConicalSeparatedRetention.annularBump R hR).rIn_pos.le)
      rw [h]; exact one_ne_zero)
  exact (ConicalSeparatedLimit.numerator_tendsto p a ha hai hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hRa))).eventually
      ((isClosed_singleton (x := (0 : ℂ))).isOpen_compl.mem_nhds hne)

theorem positive_frequency_fixed_input (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
        (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
        (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
        (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
        (q : ℂ), q≠0 ∧
        ConicalGraphProjection.projected p
          (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ).graph
          =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
            q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
              (radialCorrection (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ))
              (tangentCorrection (ConicalFiniteGauge.system p a b k ha hai hba hk.ne' hfreq c J (fun i => (hJ i).continuous) heJ)) r := by
  have hN := eventually_nonzero_baseline p a R ha hai hR (hRb.trans hba).le hν
  have hfreq : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (DynamicStaticLimit.frequencyRadius_positive (ConicalSeparatedSource.material p a) a)] with k hk
    exact (show |k| < DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a from by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk).le
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hN.and hfreq)
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  have hm : k ∈ ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd
  obtain ⟨hN,hfreq⟩ := hsub hm
  refine ⟨hfreq,?_⟩
  apply exists_nonzero_coefficient p a b R k ha (hR.trans hRb) hai hba hRb hν hk hfreq
    (ConicalSeparatedRetention.annularBump R hR)
    (ConicalSeparatedRetention.annularBump R hR).contDiff
    (ConicalSeparatedRetention.annularBump R hR).hasCompactSupport
    (ConicalSeparatedRetention.annularBump_support R hR)
  rw [ConicalGaugeStability.baseline_numerator]
  exact hN


end OQ14.ConicalFixedFiniteInput
#print axioms OQ14.ConicalFixedFiniteInput.exists_nonzero_numerator
#print axioms OQ14.ConicalFixedFiniteInput.exists_nonzero_coefficient

#print axioms OQ14.ConicalFixedFiniteInput.eventually_nonzero_baseline
#print axioms OQ14.ConicalFixedFiniteInput.positive_frequency_fixed_input
