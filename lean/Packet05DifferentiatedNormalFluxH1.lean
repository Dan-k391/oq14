import Packet05GraphFluxTangential
import Packet05DifferentiatedSourceRegularity

/-! H¹ of the tangentially differentiated conserved normal flux, derived
from the differentiated regional transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferentiatedNormalFluxH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalDifferentiatedScalar
  OQ14.Packet05GraphNormalFluxH1 OQ14.Packet05GraphFluxTangential
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05DifferentiatedScalarEquation
  OQ14.Packet05DifferentiatedSourceRegularity OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator

theorem differentiated_normal_flux_h1 (V : Set Space) (hV : IsOpen V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F Ci C0 C1 Ci0 Ci1 Fi Fi0 Fi1 : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) (hi : i ≠ 2)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hCi : ∀ j, HasWeakPartial (C j) (Ci j) i)
    (hC0 : ∀ j, HasWeakPartial (C j) (C0 j) 0)
    (hC1 : ∀ j, HasWeakPartial (C j) (C1 j) 1)
    (hCi0 : ∀ j, HasWeakPartial (Ci j) (Ci0 j) 0)
    (hCi1 : ∀ j, HasWeakPartial (Ci j) (Ci1 j) 1)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hFi0 : ∀ j, HasWeakPartial (Fi j) (Fi0 j) 0)
    (hFi1 : ∀ j, HasWeakPartial (Fi j) (Fi1 j) 1)
    (χ : Test) (hχV : tsupport χ.function ⊆ V) :
    ∃ D : L2Vector, ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact
        (flux A Ci d hd 2-differentiatedSource A hA2 C Fi d hd i 2)) (D j) j := by
  let R := differentiatedSource A hA2 C Fi d hd i
  let R0 : L2Vector := fun j => Fi0 j - mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) C0 j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) 0) C j)
  let R1 : L2Vector := fun j => Fi1 j - mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) C1 j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) 1) C j)
  have hR0 (j : Fin 3) : HasWeakPartial (R j) (R0 j) 0 :=
    differentiated_source_tangential_partial A hA2 hA3 C C0 Fi Fi0 d hd i 0 (by decide) hC0 hFi0 j
  have hR1 (j : Fin 3) : HasWeakPartial (R j) (R1 j) 1 :=
    differentiated_source_tangential_partial A hA2 hA3 C C1 Fi Fi1 d hd i 1 (by decide) hC1 hFi1 j
  have hdivi : HasDivergenceOn V (fun j => flux A Ci d hd j-R j) 0 := by
    apply regional_differentiated_scalar_equation V hV A hA2 C C Ci F F Fi 0 d hd i hi hdiv
    · filter_upwards [Lp.coeFn_zero ℂ (2 : ENNReal) (volume : Measure Space)] with x hx _
      exact hx
    · intro j
      filter_upwards with x _
      rfl
    · intro j
      filter_upwards with x _
      rfl
    · exact hCi
    · exact hFi
  exact conserved_normal_flux_h1 V A hA2 Ci R Ci0 Ci1 R0 R1 d hd hdivi hCi0 hCi1 hR0 hR1 χ hχV

end OQ14.Packet05DifferentiatedNormalFluxH1
#print axioms OQ14.Packet05DifferentiatedNormalFluxH1.differentiated_normal_flux_h1
