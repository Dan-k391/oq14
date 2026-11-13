import Packet05ActualCompactGreenH2

/-! H² for the actual complex-frequency Maxwell correction field, on any
compact smooth cutoff, from the compact L² material source alone. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualCorrectionH2
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05ActualCompactGreenH2

theorem weak_partial_smul (a : ℂ) (u v : L2Scalar) (j : Fin 3)
    (h : HasWeakPartial u v j) : HasWeakPartial (a • u) (a • v) j := by
  intro φ
  have hh := congrArg (fun x : ℂ => a*x) (h φ)
  simp only [map_smul, smul_eq_mul] at ⊢
  linear_combination hh

theorem correction_component_compact_h2 (z : ℂ) (R S : ℝ)
    (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R)
    (k : Fin 3) :
    ∃ U : L2Scalar, ∃ G : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ j, HasWeakPartial U (G j) j) ∧
      (∀ i j, HasWeakPartial (G i) (H i j) j) ∧
      (∀ᵐ x ∂volume, U x = χ.function x * Packet06ComplexPotential.correction z ρ x k) := by
  obtain ⟨U, G, H, hG, hH, hU⟩ := actual_compact_green_h2 z R S
    (NewtonL2.physicalCoordinate F k) (ρ k) (hF k) (hρ k) (hc k) (hs k) χ hχ2 hχR
  refine ⟨z^2 • U, fun j => z^2 • G j, fun i j => z^2 • H i j,
    (fun j => weak_partial_smul _ _ _ _ (hG j)),
    (fun i j => weak_partial_smul _ _ _ _ (hH i j)), ?_⟩
  filter_upwards [Lp.coeFn_smul (z^2) U, hU] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul, Packet06ComplexPotential.correction]
  rw [hy]
  ring

end OQ14.Packet05ActualCorrectionH2
#print axioms OQ14.Packet05ActualCorrectionH2.weak_partial_smul
#print axioms OQ14.Packet05ActualCorrectionH2.correction_component_compact_h2
