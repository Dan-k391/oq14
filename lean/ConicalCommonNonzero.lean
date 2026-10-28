import ConicalCommonExtraction

/-! The actual common-material local numerator retains its nonzero static limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalCommonNonzero
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem eventually_numerator_ne_zero (i : ι) (R T b r : ℝ) (hR0 : 0 ≤ R) (hRT : 0 ≤ R+T)
    (hr : r < b) (hb : b < a i) (hν : (p i).exponent < 1)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) r)
    (hne : ConicalAnnularCoefficient.fieldPair (p i) ζ hζ hc (ConicalStaticVolume.electric (p i)) ≠ 0) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ (hk : k ≠ 0)
      (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R),
      ConicalCoefficientStability.numerator (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep
        i i R T k b hR0 hk hb hfreq hR hT hai) ζ hζ hc ≠ 0 := by
  obtain ⟨C,hC,hbound⟩ := ConicalCommonExtraction.numerator_near_total (p i) hν r ζ hζ hc hs
  let target := ConicalAnnularCoefficient.fieldPair (p i) ζ hζ hc (ConicalStaticVolume.electric (p i))
  let D := (‖ConicalCommonRetention.staticSource p a center B hB hcontrast ha hsep i‖+1) *
    ‖ScalarPotentialBound.cutoff 0 ((max r 0 + ‖center i‖)+T)‖
  have hD : 0 ≤ D := mul_nonneg (by positivity) (norm_nonneg _)
  have heps : 0 < ‖target‖/2 := div_pos (norm_pos_iff.mpr hne) (by norm_num)
  have hpair := ConicalCommonTipConvergence.tipPair_tendsto p a center B hB hcontrast ha hsep i R T hR0 hRT ζ hζ hc
  have hsmall : Tendsto (fun k : ℝ => C*(k^2*D)) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 0) (𝓝 0)).pow 2).mul_const D)
  filter_upwards [hpair.eventually (Metric.ball_mem_nhds target heps),
    hsmall.eventually (Metric.ball_mem_nhds 0 heps),
    ConicalCommonRetention.correction_eventually_bound p a center B hB hcontrast ha hsep i i R T r hR0 hRT hT]
    with k hp hsm hcorr hk hfreq
  let s := ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk hb hfreq hR hT hai
  have hM : 0 ≤ k^2*D := mul_nonneg (sq_nonneg _) hD
  have hw : ∀ j x, x ∈ closedBall (0 : Space) r → ‖s.correction j x‖ ≤ k^2*D := by
    intro j x hx
    have hxb : x ∈ ball (0 : Space) b := closedBall_subset_ball hr hx
    have hxi : x ∈ ball (0 : Space) (p i).cutoff.rIn := ball_subset_ball (hb.trans (hai i)).le hxb
    change ‖ConicalGradientGraph.bump (p i).cutoff x *
      ConicalCommonResponse.centeredCorrection p a center B hB hcontrast ha hsep i i R T k x j‖ ≤ _
    rw [(ConicalGradientGraph.bump_inner (p i).cutoff x hxi).1, one_mul]
    exact hcorr j x hx
  have hn := hbound s hr.le (k^2*D) hM hw
  have htotal : ConicalLocalStability.totalPair s ζ hζ hc =
      ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc :=
    ConicalCommonPairing.totalPair_eq p a center B hB hcontrast ha hsep i R T k b hR0 hk hb hfreq hR hT hai ζ hζ hc
      (hs.trans (Ioo_subset_Ioo_right hr.le))
  rw [htotal] at hn
  have hp' : ‖ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc-target‖ < ‖target‖/2 := by
    simpa [mem_ball, dist_eq_norm] using hp
  have hsm' : C*(k^2*D) < ‖target‖/2 := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hM)] using hsm
  intro hz
  rw [hz, zero_sub, norm_neg] at hn
  have hh := norm_sub_le target (ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc)
  have he : target - (target - ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc) =
      ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc := by ring
  have ht := norm_add_le (target-ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc)
    (ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc)
  have hrev : ‖target-ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc‖ < ‖target‖/2 := by
    rwa [norm_sub_rev]
  have : ‖target‖ ≤ ‖target-ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc‖ +
      ‖ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc‖ := by
    simpa using ht
  linarith

theorem eventually_nonzero_coefficient (i : ι) (R T b : ℝ) (hR0 : 0 ≤ R) (hRT : 0 ≤ R+T)
    (hb0 : 0 < b) (hb : b < a i) (hν : (p i).exponent < 1)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ (hk : k ≠ 0)
      (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R),
      ConicalIntrinsicCoefficient.coefficient
        (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk hb hfreq hR hT hai)
        hb0 (hb.trans (hai i)) hν ≠ 0 := by
  let r : ℝ := b/2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr : r < b := by dsimp [r]; linarith
  let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump r hr0
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (ConicalSeparatedRetention.annularBump r hr0).contDiff
  have hc : HasCompactSupport ζ := (ConicalSeparatedRetention.annularBump r hr0).hasCompactSupport
  have hs : tsupport ζ ⊆ Ioo (0 : ℝ) r := ConicalSeparatedRetention.annularBump_support r hr0
  have hne := ConicalStaticCoefficient.static_pairing_ne_zero (p i) hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right (hr.trans (hb.trans (hai i))).le))
    (fun _ => (ConicalSeparatedRetention.annularBump r hr0).nonneg) (r/2) (by linarith)
    (by
      have hv : ζ (r/2) = 1 := (ConicalSeparatedRetention.annularBump r hr0).one_of_mem_closedBall (by
        simp only [mem_closedBall, dist_self]; exact (ConicalSeparatedRetention.annularBump r hr0).rIn_pos.le)
      rw [hv]; exact one_ne_zero)
  filter_upwards [eventually_numerator_ne_zero p a center B hB hcontrast ha hsep i R T b r hR0 hRT hr hb hν hR hT hai ζ hζ hc hs hne]
    with k hn hk hfreq
  let s := ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk hb hfreq hR hT hai
  obtain ⟨q, hq, he⟩ := ConicalLocalCoefficient.coefficient_identity s hb0 (hb.trans (hai i)) hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hr.le))
  have hq0 : q ≠ 0 := by
    intro hz
    have hh := hn hk hfreq
    apply hh
    change ConicalLocalCoefficient.gradientPair s ζ hζ hc - ConicalLocalCoefficient.particularPair s ζ = 0
    rw [he, hz]
    ring
  have hqeq := ConicalIntrinsicCoefficient.coefficient_unique s hb0 (hb.trans (hai i)) hν q hq
  exact hqeq ▸ hq0

theorem simultaneous_baseline_nonzero (R T : ℝ) (b : ι → ℝ) (hR0 : 0 ≤ R) (hRT : 0 ≤ R+T)
    (hb0 : ∀ i, 0 < b i) (hb : ∀ i, b i < a i) (hν : ∀ i, (p i).exponent < 1)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ i, a i < (p i).cutoff.rIn) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, ∀ (hk : 0 < k), k < δ →
      ∀ i : ι, ∃ hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius
        (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R,
      ConicalIntrinsicCoefficient.coefficient
        (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k (b i)
          hR0 (ne_of_gt hk) (hb i) hfreq hR hT hai) (hb0 i) ((hb i).trans (hai i)) (hν i) ≠ 0 := by
  have he : ∀ᶠ k : ℝ in 𝓝 0, ∀ i : ι, ∀ (hk : k ≠ 0)
      (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R),
      ConicalIntrinsicCoefficient.coefficient
        (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k (b i)
          hR0 hk (hb i) hfreq hR hT hai) (hb0 i) ((hb i).trans (hai i)) (hν i) ≠ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_nonzero_coefficient p a center B hB hcontrast ha hsep
      i R T (b i) hR0 hRT (hb0 i) (hb i) (hν i) hR hT hai)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp he
  let d := DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R
  have hd : 0 < d := DynamicStaticLimit.frequencyRadius_positive _ _
  refine ⟨min δ d, lt_min hδ hd, ?_⟩
  intro k hk hkd i
  have hkδ : k ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hk] using hkd.trans_le (min_le_left _ _)
  have hkfreq : |k| ≤ d := by rw [abs_of_pos hk]; exact (hkd.trans_le (min_le_right _ _)).le
  exact ⟨hkfreq, hsub hkδ i hk.ne' hkfreq⟩

end OQ14.ConicalCommonNonzero
#print axioms OQ14.ConicalCommonNonzero.eventually_numerator_ne_zero
#print axioms OQ14.ConicalCommonNonzero.eventually_nonzero_coefficient
#print axioms OQ14.ConicalCommonNonzero.simultaneous_baseline_nonzero
