import Packet05GraphNormalFluxH1
import Packet05QuantitativeCutoffRepresentative

/-! Explicit derivative array for a localized conserved normal flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ExplicitNormalFluxDerivative
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05RegionalNormalFlux
  Packet05LocalPartialProduct Packet05ScalarDielectricFlux Packet05WeightedMatrixDerivative
  Packet05GraphPiolaH2 Packet05QuantitativeCutoffRepresentative

def tangentFlux (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C _F Ci Fi : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) : L2Scalar :=
  Packet05FlatWeight.mulWeight d hd
    (Packet05TensorCommutator.matrixField A Ci j +
      Packet05TensorCommutator.matrixField (Packet05MatrixWeakDerivative.derivativeMatrix A hA i) C j)-Fi j

def normalDerivativeArray (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F C0 C1 F0 F1 : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) : Fin 3 → L2Scalar :=
  ![tangentFlux A hA C F C0 F0 d hd 0 2,
    tangentFlux A hA C F C1 F1 d hd 1 2,
    0-tangentFlux A hA C F C0 F0 d hd 0 0-tangentFlux A hA C F C1 F1 d hd 1 1]

theorem explicit_normal_flux_h1 (V : Set Space) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F C0 C1 F0 F1 : L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC0 : ∀ j, HasWeakPartial (C j) (C0 j) 0)
    (hC1 : ∀ j, HasWeakPartial (C j) (C1 j) 1)
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (χ : Test) (hχV : tsupport χ.function ⊆ V) :
    ∀ i, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (flux A C d hd 2-F 2))
      (firstArray (flux A C d hd 2-F 2) (normalDerivativeArray A hA C F C0 C1 F0 F1 d hd) χ i) i := by
  let P : L2Vector := fun j => flux A C d hd j-F j
  let P0 : L2Vector := tangentFlux A hA C F C0 F0 d hd 0
  let P1 : L2Vector := tangentFlux A hA C F C1 F1 d hd 1
  have hp0 (j : Fin 3) : HasWeakPartial (P j) (P0 j) 0 :=
    weak_partial_sub _ _ _ _ 0 (weighted_matrix_tangential_partial A hA C C0 d hd 0 j (by decide) hC0) (hF0 j)
  have hp1 (j : Fin 3) : HasWeakPartial (P j) (P1 j) 1 :=
    weak_partial_sub _ _ _ _ 1 (weighted_matrix_tangential_partial A hA C C1 d hd 1 j (by decide) hC1) (hF1 j)
  have hpn : HasPartialOn V (P 2) (0-P0 0-P1 1) 2 :=
    regional_normal_flux_partial V P 0 (P0 0) (P1 1) hdiv
      (global_partial_on V _ _ 0 (hp0 0)) (global_partial_on V _ _ 1 (hp1 1))
  intro i
  fin_cases i
  · exact local_cutoff_weak_partial V χ hχV (P 2) (P0 2) 0 (global_partial_on V _ _ 0 (hp0 2))
  · exact local_cutoff_weak_partial V χ hχV (P 2) (P1 2) 1 (global_partial_on V _ _ 1 (hp1 2))
  · exact local_cutoff_weak_partial V χ hχV (P 2) (0-P0 0-P1 1) 2 hpn

end OQ14.Packet05ExplicitNormalFluxDerivative
#print axioms OQ14.Packet05ExplicitNormalFluxDerivative.explicit_normal_flux_h1
