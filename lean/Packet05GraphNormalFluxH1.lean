import Packet05BinaryPhaseDerivative
import Packet05RegionalNormalFlux
import Packet05LocalPartialProduct

/-! The conserved graph-normal flux has full H¹ after an interior cutoff.
Its normal derivative is obtained from the actual scalar divergence equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphNormalFluxH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalNormalFlux OQ14.Packet05LocalPartialProduct
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05WeightedMatrixDerivative
  OQ14.Packet05GraphPiolaH2

theorem conserved_normal_flux_h1 (V : Set Space) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F C0 C1 F0 F1 : L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC0 : ∀ j, HasWeakPartial (C j) (C0 j) 0)
    (hC1 : ∀ j, HasWeakPartial (C j) (C1 j) 1)
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (χ : Test) (hχV : tsupport χ.function ⊆ V) :
    ∃ D : L2Vector, ∀ i, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (flux A C d hd 2-F 2)) (D i) i := by
  let P : L2Vector := fun j => flux A C d hd j-F j
  let P0 : L2Vector := fun j => Packet05FlatWeight.mulWeight d hd
    (Packet05TensorCommutator.matrixField A C0 j +
      Packet05TensorCommutator.matrixField (Packet05MatrixWeakDerivative.derivativeMatrix A hA 0) C j)-F0 j
  let P1 : L2Vector := fun j => Packet05FlatWeight.mulWeight d hd
    (Packet05TensorCommutator.matrixField A C1 j +
      Packet05TensorCommutator.matrixField (Packet05MatrixWeakDerivative.derivativeMatrix A hA 1) C j)-F1 j
  have hp0 (j : Fin 3) : HasWeakPartial (P j) (P0 j) 0 :=
    weak_partial_sub _ _ _ _ 0 (weighted_matrix_tangential_partial A hA C C0 d hd 0 j (by decide) hC0) (hF0 j)
  have hp1 (j : Fin 3) : HasWeakPartial (P j) (P1 j) 1 :=
    weak_partial_sub _ _ _ _ 1 (weighted_matrix_tangential_partial A hA C C1 d hd 1 j (by decide) hC1) (hF1 j)
  have hpn : HasPartialOn V (P 2) (0-P0 0-P1 1) 2 :=
    regional_normal_flux_partial V P 0 (P0 0) (P1 1) hdiv
      (global_partial_on V _ _ 0 (hp0 0)) (global_partial_on V _ _ 1 (hp1 1))
  have hall (i : Fin 3) : ∃ D, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (P 2)) D i := by
    fin_cases i
    · exact ⟨_, local_cutoff_weak_partial V χ hχV (P 2) (P0 2) 0 (global_partial_on V _ _ 0 (hp0 2))⟩
    · exact ⟨_, local_cutoff_weak_partial V χ hχV (P 2) (P1 2) 1 (global_partial_on V _ _ 1 (hp1 2))⟩
    · exact ⟨_, local_cutoff_weak_partial V χ hχV (P 2) (0-P0 0-P1 1) 2 hpn⟩
  classical
  choose D hD using hall
  exact ⟨D,hD⟩

end OQ14.Packet05GraphNormalFluxH1
#print axioms OQ14.Packet05GraphNormalFluxH1.conserved_normal_flux_h1
