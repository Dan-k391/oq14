import Packet05ExplicitDifferentiatedNormalFlux
import Packet05QuantitativeNormalFlux

/-! Explicit arrays for quantitative normal-flux continuity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05NormalFluxArrays
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05GraphFluxTangential Packet05CutoffPlateauDerivative
  Packet05ScalarDielectricFlux Packet05DifferentiatedScalarEquation Packet05PartialProduct
  Packet05MatrixWeakDerivative Packet05FlatWeight Packet05TensorCommutator
  Packet05DifferentiatedSourceRegularity Packet05CurlSourceH1 Packet05LocalDerivative
  Packet05ExplicitNormalFluxDerivative Packet05QuantitativeCutoffRepresentative

def firstFluxArray (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (d : ℝ) (hd : 0 ≤ d) (η : Test) : Fin 3 → L2Scalar :=
  firstArray (flux A C d hd 2-F 2)
    (normalDerivativeArray A hA2 C F (C1 0) (C1 1) (F1 0) (F1 1) d hd) η

def sourceDerivative (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C Ct Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i t : Fin 3) : L2Vector :=
  fun j => Fit j - mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) Ct j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j)

def secondFluxArray (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C _F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (χ : Test) (i j : Fin 3) : L2Scalar :=
  let R := differentiatedSource A hA2 C (F1 i) d hd i
  firstArray (flux A (C1 i) d hd 2-R 2)
    (normalDerivativeArray A hA2 (C1 i) R (C2 i 0) (C2 i 1)
      (sourceDerivative A hA2 hA3 C (C1 0) (F2 i 0) d hd i 0)
      (sourceDerivative A hA2 hA3 C (C1 1) (F2 i 1) d hd i 1) d hd) χ j

theorem normal_flux_arrays (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (C j) (C1 i j) i)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hC2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (η χ : Test) (hηV : tsupport η.function ⊆ V)
    (hηW : ∀ x ∈ W, η.function x = 1) (hχW : tsupport χ.function ⊆ W) :
    (∀ i, HasWeakPartial (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2))
      (firstFluxArray A hA2 C F C1 F1 d hd η i) i) ∧
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (firstFluxArray A hA2 C F C1 F1 d hd η i))
      (secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i j) j) := by
  let P : L2Vector := fun j => flux A C d hd j-F j
  let D := firstFluxArray A hA2 C F C1 F1 d hd η
  let DP (i : Fin 3) : L2Vector := fun j =>
    flux A (C1 i) d hd j-differentiatedSource A hA2 C (F1 i) d hd i j
  have hD : ∀ i, HasWeakPartial (scaleL2 η.function η.regular.continuous η.compact (P 2)) (D i) i :=
    explicit_normal_flux_h1 V A hA2 C F (C1 0) (C1 1) (F1 0) (F1 1) d hd hdiv
      (hC1 0 (by decide)) (hC1 1 (by decide)) (hF1 0 (by decide)) (hF1 1 (by decide)) η hηV
  refine ⟨hD,?_⟩
  intro i hi j
  have hPi : HasWeakPartial (P 2) (DP i 2) i :=
    graph_flux_tangential_partial A hA2 C (C1 i) F (F1 i) d hd i 2 hi (hC1 i hi) (hF1 i hi)
  have hDi : D i = cutoffProductDerivative η (P 2) (DP i 2) i := by
    apply weak_partial_unique _ _ _ i (hD i)
    exact cutoff_weak_partial η (P 2) (DP i 2) i hPi
  change HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) _ j
  rw [hDi, cutoff_derivative_plateau W hW η χ hηW hχW (P 2) (DP i 2) i]
  have hdivW : HasDivergenceOn W (fun j => flux A C d hd j-F j) 0 :=
    fun φ hφ => hdiv φ (hφ.trans hWV)
  exact Packet05ExplicitDifferentiatedNormalFlux.explicit_differentiated_normal_flux_h1 W hW A hA2 hA3
    C F (C1 i) (C1 0) (C1 1) (C2 i 0) (C2 i 1) (F1 i) (F2 i 0) (F2 i 1) d hd i hi hdivW
    (hC1 i hi) (hC1 0 (by decide)) (hC1 1 (by decide))
    (hC2 i hi 0 (by decide)) (hC2 i hi 1 (by decide))
    (hF1 i hi) (hF2 i hi 0 (by decide)) (hF2 i hi 1 (by decide)) χ hχW j

end OQ14.Packet05NormalFluxArrays
#print axioms OQ14.Packet05NormalFluxArrays.normal_flux_arrays
