import Packet05ScalarNewtonEmbedding

/-! A genuine L² static Newton-Hessian component for one scalar source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ScalarNewtonPairing
open MeasureTheory OQ14.Maxwell OQ14.Packet05ScalarNewtonEmbedding
open scoped SchwartzMap

theorem scalar_newton_hessian_pairing (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (i j : Fin 3) (g : 𝓢(Space, ℂ)) :
    (∫ x, NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (scalarSource F j)) i x * g x) =
      NewtonConvolution.weakConvolution (F : Space → ℂ) i j g := by
  have hi : ∀ k, Integrable (NewtonL2.physicalCoordinate (scalarSource F j) k : Space → ℂ) := by
    intro k
    rw [scalarSource_coordinate]
    split
    · exact hF
    · exact (integrable_zero Space ℂ volume).congr (Lp.coeFn_zero ℂ 2 volume).symm
  rw [NewtonL1L2.newtonOperator_spatial_pairing _ hi]
  simp only [scalarSource_coordinate]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb, NewtonConvolution.weakConvolution]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end OQ14.Packet05ScalarNewtonPairing
#print axioms OQ14.Packet05ScalarNewtonPairing.scalar_newton_hessian_pairing
