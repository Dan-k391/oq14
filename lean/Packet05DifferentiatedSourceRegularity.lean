import Packet05DifferentiatedScalarEquation
import Packet05WeakFourier

/-! The forcing created by differentiating the scalar transmission equation
has the needed second tangential weak derivative and compact support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferentiatedSourceRegularity
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.WeakTranslations OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator
  OQ14.Packet05MatrixWeakDerivative OQ14.Packet05WeightedMatrixDerivative
  OQ14.Packet05DifferentiatedScalarEquation OQ14.Packet05WeakFourier

theorem weight_compact (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) (hu : CompactRepresentative u) :
    CompactRepresentative (mulWeight d hd u) := by
  obtain ⟨f,hf,he⟩ := hu
  refine ⟨fun x => weight d x * f x,hf.mul_left,?_⟩
  filter_upwards [mulWeight_ae d hd u, he] with x hw hx
  rw [hw,hx]

theorem derivativeMatrix_c2 (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (i j k : Fin 3) :
    ContDiff ℝ 2 ((derivativeMatrix A hA2 i) j k).function := by
  have hh : ContDiff ℝ 2 (fderiv ℝ (A j k).function) :=
    (contDiff_succ_iff_fderiv (n := 2)).mp (hA3 j k) |>.2.2
  exact hh.clm_apply contDiff_const

theorem differentiated_source_compact (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hDF : CompactRepresentative (DF j)) :
    CompactRepresentative (differentiatedSource A hA2 C DF d hd i j) := by
  apply compact_sub hDF
  exact weight_compact d hd _ (matrixField_compact (derivativeMatrix A hA2 i) C j)

theorem differentiated_source_tangential_partial (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C DC DF DDF : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i t : Fin 3) (ht : t ≠ 2)
    (hC : ∀ k, HasWeakPartial (C k) (DC k) t)
    (hDF : ∀ j, HasWeakPartial (DF j) (DDF j) t) (j : Fin 3) :
    HasWeakPartial (differentiatedSource A hA2 C DF d hd i j)
      (DDF j - mulWeight d hd (matrixField (derivativeMatrix A hA2 i) DC j +
        matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j)) t := by
  have hw := weighted_matrix_tangential_partial (derivativeMatrix A hA2 i)
    (derivativeMatrix_c2 A hA2 hA3 i) C DC d hd t j ht hC
  have hf := hDF j
  intro φ
  have hw := hw φ
  have hf := hf φ
  simp only [differentiatedSource, map_sub]
  linear_combination hf - hw

end OQ14.Packet05DifferentiatedSourceRegularity
#print axioms OQ14.Packet05DifferentiatedSourceRegularity.weight_compact
#print axioms OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2
#print axioms OQ14.Packet05DifferentiatedSourceRegularity.differentiated_source_compact
#print axioms OQ14.Packet05DifferentiatedSourceRegularity.differentiated_source_tangential_partial
