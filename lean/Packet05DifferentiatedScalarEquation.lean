import Packet05WeightedMatrixDerivative
import Packet05DivergenceCommutation
import Packet05GraphPiolaLinear
import Packet05ScalarDielectricFlux
import Packet05ScalarEnergyIdentity

/-! Tangential differentiation of the actual binary variable-matrix scalar
equation, retaining the coefficient-derivative source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferentiatedScalarEquation
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05DivergenceCommutation
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarEnergyIdentity

def differentiatedSource (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) : L2Vector := fun j =>
  DF j - mulWeight d hd (matrixField (derivativeMatrix A hA i) C j)

theorem differentiated_scalar_equation (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DC F DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (D DD : L2Scalar) (i : Fin 3) (hi : i ≠ 2)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) D)
    (hC : ∀ j, HasWeakPartial (C j) (DC j) i)
    (hF : ∀ j, HasWeakPartial (F j) (DF j) i)
    (hD : HasWeakPartial D DD i) :
    HasWeakDivergence (fun j => flux A DC d hd j - differentiatedSource A hA C DF d hd i j) DD := by
  have hP (j : Fin 3) : HasWeakPartial (flux A C d hd j - F j)
      (flux A DC d hd j - differentiatedSource A hA C DF d hd i j) i := by
    have hw := weighted_matrix_tangential_partial A hA C DC d hd i j hi hC
    have hf := hF j
    intro φ
    have hw := hw φ
    have hf := hf φ
    rw [mulWeight_add] at hw
    simp only [map_add] at hw
    simp only [flux, differentiatedSource, map_sub]
    linear_combination hw - hf
  exact partial_commutes_weakDivergence _ _ D DD i hdiv hP hD

end OQ14.Packet05DifferentiatedScalarEquation
#print axioms OQ14.Packet05DifferentiatedScalarEquation.differentiated_scalar_equation
