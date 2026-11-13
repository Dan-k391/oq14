import Packet05GraphNormalFluxH1
import Packet05RegionalDifferentiatedScalar

/-! The tangential derivative of the conserved normal flux is the normal
flux of the actually differentiated scalar equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05GraphFluxTangential
open OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurlCompact
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05DifferentiatedScalarEquation
  OQ14.Packet05ScalarEnergyIdentity

theorem graph_flux_tangential_partial (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DC F DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hi : i ≠ 2)
    (hC : ∀ j, HasWeakPartial (C j) (DC j) i)
    (hF : ∀ j, HasWeakPartial (F j) (DF j) i) :
    HasWeakPartial (flux A C d hd j-F j)
      (flux A DC d hd j-differentiatedSource A hA C DF d hd i j) i := by
  have hw := weighted_matrix_tangential_partial A hA C DC d hd i j hi hC
  have hf := hF j
  intro φ
  have hw := hw φ
  have hf := hf φ
  rw [mulWeight_add] at hw
  simp only [map_add] at hw
  simp only [flux, differentiatedSource, map_sub]
  linear_combination hw-hf

end OQ14.Packet05GraphFluxTangential
#print axioms OQ14.Packet05GraphFluxTangential.graph_flux_tangential_partial
