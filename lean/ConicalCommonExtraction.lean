import ConicalCommonPairing

/-! Quantitative extraction error from a small local correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonExtraction
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space

theorem zero_correctionPair {p : Data} {b : ℝ} (s : System p b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    ConicalLocalStability.correctionPair (ConicalProjectionLinear.sub s s) ζ hζ hc = 0 := by
  rw [ConicalLocalStability.correctionPair_sub, sub_self]

theorem zero_particularPair {p : Data} {b : ℝ} (s : System p b) (ζ : ℝ → ℝ) :
    ConicalLocalCoefficient.particularPair (ConicalProjectionLinear.sub s s) ζ = 0 := by
  simp only [ConicalLocalCoefficient.particularPair, ConicalProjectionLinear.radialCorrection_sub,
    ConicalProjectionLinear.tangentCorrection_sub, sub_self]
  simp [ConicalRadialParticular.particular, ConicalRadialParticular.leftPrimitive,
    ConicalRadialParticular.rightPrimitive, ConicalRadialParticular.minusForcing,
    ConicalRadialParticular.plusForcing, ConePowerPrimitive.primitive]

theorem numerator_near_total (p : Data) (hν : p.exponent < 1) (R : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : ℝ} (s : System p b), R ≤ b → ∀ M : ℝ, 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x‖ ≤ M) →
      ‖ConicalCoefficientStability.numerator s ζ hζ hc - ConicalLocalStability.totalPair s ζ hζ hc‖ ≤ C*M := by
  obtain ⟨C,hC,hpart⟩ := ConicalCoefficientStability.particularPair_difference_bound p hν R ζ hζ hc hs
  let mass := ConicalAnnularCoefficient.testMass p ζ
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => norm_nonneg _))
  refine ⟨mass+C, add_nonneg hmass hC, ?_⟩
  intro b s hRb M hM hw
  let z := ConicalProjectionLinear.sub s s
  have hz (i : Fin 3) (x : Space) : z.correction i x = 0 := by simp [z, ConicalProjectionLinear.sub]
  have hd : ∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-z.correction i x‖ ≤ M := by
    intro i x hx
    simpa only [hz, sub_zero] using hw i x hx
  have hcp := ConicalLocalStability.correctionPair_difference_bound s z R M hM hd ζ hζ hc hs
  rw [show ConicalLocalStability.correctionPair z ζ hζ hc = 0 from zero_correctionPair s ζ hζ hc, sub_zero] at hcp
  have hp := hpart s z hRb M hM hd
  rw [show ConicalLocalCoefficient.particularPair z ζ = 0 from zero_particularPair s ζ, sub_zero] at hp
  have he : ConicalCoefficientStability.numerator s ζ hζ hc - ConicalLocalStability.totalPair s ζ hζ hc =
      -(ConicalLocalStability.correctionPair s ζ hζ hc)-ConicalLocalCoefficient.particularPair s ζ := by
    rw [ConicalCoefficientStability.numerator, ConicalLocalStability.gradientPair_eq]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (by simpa only [norm_neg] using hcp) hp).trans_eq (by dsimp [mass]; ring))

end OQ14.ConicalCommonExtraction
#print axioms OQ14.ConicalCommonExtraction.zero_correctionPair
#print axioms OQ14.ConicalCommonExtraction.zero_particularPair
#print axioms OQ14.ConicalCommonExtraction.numerator_near_total
