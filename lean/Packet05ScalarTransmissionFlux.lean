import Packet05ScalarTransmissionCommutator
import Packet05ForcedDifferenceGreen

/-! Tangential differentiation of a flat-jump scalar transmission flux with
smooth matrix factor: the material jump is retained exactly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarTransmissionFlux
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator
  OQ14.Packet05TensorCommutator OQ14.Packet05ScalarTransmissionCommutator
  OQ14.MaxwellWeakTranslation

theorem flat_jump_matrix_quotient (A : Fin 3 → Fin 3 → Test) (C W : L2Vector)
    (d : ℝ) (i j : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0) (b : ℝ)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (hW : ∀ q, (fun x => W q x) =ᵐ[volume]
      fun x => flatWeight d x * matrixField A C q x) :
    (fun x => quotientVector W i h j x) =ᵐ[volume]
      fun x => flatWeight d x *
        (matrixField A (fun l => quotient (C l) i h) j x + matrixResidual A C i j h hh b hb x) := by
  have hw := quotient_commutes_invariant_weight W (matrixField A C) (flatWeight d) i h
    (flatWeight_tangential d i hi h) hW j
  have he := matrix_quotient_decomposition A C i j h hh b hb
  filter_upwards [hw, Lp.coeFn_add (matrixField A (fun l => quotient (C l) i h) j)
    (matrixResidual A C i j h hh b hb)] with x hx ha
  rw [hx]
  change flatWeight d x * quotient (matrixField A C j) i h x = _
  rw [he, ha]
  rfl

end OQ14.Packet05ScalarTransmissionFlux
#print axioms OQ14.Packet05ScalarTransmissionFlux.flat_jump_matrix_quotient
