import ConicalFiniteIlluminationPeaks
import ConicalFamily

/-! Prescribed finite contrast and cap angle with actual finite Maxwell illumination volume peaks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalFiniteIlluminationFamily
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalRungeClosure OQ14.ConicalSeparatedRounding OQ14.ConicalFiniteIlluminationPeaks
open scoped Topology
abbrev Space := Maxwell.Space

theorem exists_prescribed (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (p : Data) (δ : ℝ), p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧
      p.exponent ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      δ ≤ MaterialVolumeLimit.commonRadius d (χ.rIn/2) ∧
      (∀ n, (material p (χ.rIn/2) n).bound=d) ∧
      (∀ n x, permittivity p (χ.rIn/2) n x ∈ Icc (1 : ℝ) (1+d)) ∧
      (∀ n x, ‖x‖ ≤ ConicalTipRounding.radius n → permittivity p (χ.rIn/2) n x=1) ∧
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (permittivity p (χ.rIn/2) n)
        (ball (0 : Space) (ConicalTipRounding.radius n))) ∧
      (∀ n x, x ∉ closedBall (0 : Space) (χ.rIn/2) → permittivity p (χ.rIn/2) n x=1) ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ χ.rIn/2 → ∀ M : ℝ,
      ∀ᶠ n : ℕ in atTop, ∃ (b : WaveIndex →₀ ℂ) (e h : DomainCurl.HCurl (ball (0 : Space) (χ.rIn/2))),
        (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) (χ.rIn/2))]
          fun x => electric p (χ.rIn/2) k n b x j) ∧
        (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) (χ.rIn/2))]
          fun x => magnetic p (χ.rIn/2) k n b x j) ∧
        WeakConservation.WeakMaxwell k (fun _ => 1) (permittivity p (χ.rIn/2) n) e h ∧
        0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p (χ.rIn/2) k n b x‖} := by
  obtain ⟨p,hχ,hd',ht',hν,_⟩ := ConicalFamily.exists_data χ d t hd ht ht1
  have ha : 0 < χ.rIn/2 := by linarith [χ.rIn_pos]
  have hai : χ.rIn/2 < p.cutoff.rIn := by rw [hχ]; linarith [χ.rIn_pos]
  obtain ⟨δ,hδ,hb,hpeaks⟩ := positive_frequency_rounded_finite_hcurl_peaks p (χ.rIn/2) ha hai hν
  refine ⟨p,δ,hχ,hd',ht',⟨p.exponent_pos,hν⟩,hδ,?_,?_,?_,?_,?_,?_,hpeaks⟩
  · simpa only [hd'] using hb
  · intro n
    simpa only [hd'] using material_bound p (χ.rIn/2) n
  · intro n x
    simpa only [hd'] using permittivity_bounds p (χ.rIn/2) n x
  · exact fun n x hx => permittivity_one_inner p (χ.rIn/2) n x hx
  · exact fun n => permittivity_smooth_near_tip p (χ.rIn/2) n
  · intro n x hx
    simp only [permittivity,common_support p (χ.rIn/2) n x hx,add_zero]

end OQ14.ConicalFiniteIlluminationFamily

#print axioms OQ14.ConicalFiniteIlluminationFamily.exists_prescribed
