import Packet05RegionalBinaryScalar
import Packet05LocalizedScalarForcingDerivative
import Packet05LocalCutoffMixed
import Packet05DifferentiatedSourceRegularity

/-! Explicit first and second tangential derivatives of the regional scalar
localization forcing, including cutoff and matrix commutators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05LocalizedForcingBootstrap
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct
  OQ14.Packet05LocalCutoffMixed OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05RegionalScalarLocalization OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1
  OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05DifferentiatedSourceRegularity
  OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative

def forceDerivative (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (v Dv : L2Scalar) (F DF : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) : L2Vector :=
  let hζc2 := Complex.ofRealCLM.contDiff.comp hζ2
  let R : L2Vector := fun j => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 j) v Dv i
  fun j => cutoffProductDerivative ζ.complexTest.toTest (F j) (DF j) i +
    mulWeight d hd (matrixField A R j + matrixField (derivativeMatrix A hA2 i) (cutoffCorrection ζ v) j)

theorem forcing_first_tangential (V : Set Space) (ζ : RealTest Set.univ)
    (hζ2 : ContDiff ℝ 2 ζ.function) (hζV : tsupport ζ.function ⊆ V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (v Dv : L2Scalar) (F DF : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) (hi : i ≠ 2)
    (hv : HasPartialOn V v Dv i) (hF : ∀ j, HasPartialOn V (F j) (DF j) i) :
    ∀ j, HasWeakPartial (localizedForcing ζ A v F d hd j)
      (forceDerivative ζ hζ2 A hA2 v Dv F DF d hd i j) i := by
  have hζV' : tsupport ζ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hζV
  let hζc2 := Complex.ofRealCLM.contDiff.comp hζ2
  let R : L2Vector := fun j => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 j) v Dv i
  have hR (j : Fin 3) : HasWeakPartial (cutoffCorrection ζ v j) (R j) i := by
    have hs : tsupport (derivativeCutoff ζ.complexTest.toTest hζc2 j).function ⊆ V :=
      (RegionalMaxwellHelmholtz.partial_tsupport ζ.complexTest.function j).trans hζV'
    exact local_cutoff_weak_partial V _ hs v Dv i hv
  intro j
  have hf := local_cutoff_weak_partial V ζ.complexTest.toTest hζV' (F j) (DF j) i (hF j)
  have hw := weighted_matrix_tangential_partial A hA2 (cutoffCorrection ζ v) R d hd i j hi hR
  intro φ
  have hf := hf φ
  have hw := hw φ
  change valuePair φ (_ + _) + derivativePair φ i (_ + _) = 0
  simp only [map_add,cutoffProductDerivative,cutVector,flux,R] at hf hw ⊢
  linear_combination hf+hw


theorem forcing_second_tangential (V : Set Space) (ζ : RealTest Set.univ)
    (hζ2 : ContDiff ℝ 2 ζ.function) (hζ3 : ContDiff ℝ 3 ζ.function)
    (hζV : tsupport ζ.function ⊆ V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (v Di Dt Dit : L2Scalar) (F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (i t : Fin 3) (ht : t ≠ 2)
    (hDt : HasPartialOn V v Dt t) (hDit : HasPartialOn V Di Dit t)
    (hFt : ∀ j, HasPartialOn V (F j) (Ft j) t)
    (hFit : ∀ j, HasPartialOn V (Fi j) (Fit j) t) :
    ∀ j, ∃ H : L2Scalar, HasWeakPartial
      (forceDerivative ζ hζ2 A hA2 v Di F Fi d hd i j) H t := by
  have hζV' : tsupport ζ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hζV
  let hζc2 : ContDiff ℝ 2 ζ.complexTest.function := Complex.ofRealCLM.contDiff.comp hζ2
  have hζc3 : ContDiff ℝ 3 ζ.complexTest.function := Complex.ofRealCLM.contDiff.comp hζ3
  have hder2 (j : Fin 3) : ContDiff ℝ 2 (derivativeCutoff ζ.complexTest.toTest hζc2 j).function := by
    have hh : ContDiff ℝ 2 (fderiv ℝ ζ.complexTest.function) :=
      (contDiff_succ_iff_fderiv (n := 2)).mp hζc3 |>.2.2
    exact hh.clm_apply contDiff_const
  have hderV (j : Fin 3) : tsupport (derivativeCutoff ζ.complexTest.toTest hζc2 j).function ⊆ V :=
    (RegionalMaxwellHelmholtz.partial_tsupport ζ.complexTest.function j).trans hζV'
  let R : L2Vector := fun j => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 j) v Di i
  let Rt : L2Vector := fun j =>
    cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 j) Di Dit t +
      cutoffProductDerivative (derivativeCutoff (derivativeCutoff ζ.complexTest.toTest hζc2 j) (hder2 j) i) v Dt t
  let Tcorr : L2Vector := fun j => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 j) v Dt t
  have hRt (j : Fin 3) : HasWeakPartial (R j) (Rt j) t :=
    local_cutoff_mixed V _ (hder2 j) (hderV j) v Di Dt Dit i t hDit hDt
  have hTc (j : Fin 3) : HasWeakPartial (cutoffCorrection ζ v j) (Tcorr j) t :=
    local_cutoff_weak_partial V _ (hderV j) v Dt t hDt
  let Ai := derivativeMatrix A hA2 i
  have hAi : ∀ j k, ContDiff ℝ 2 (Ai j k).function := derivativeMatrix_c2 A hA2 hA3 i
  intro j
  let HB := cutoffProductDerivative ζ.complexTest.toTest (Fi j) (Fit j) t +
    cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 i) (F j) (Ft j) t
  have hbase : HasWeakPartial (cutoffProductDerivative ζ.complexTest.toTest (F j) (Fi j) i) HB t :=
    local_cutoff_mixed V ζ.complexTest.toTest hζc2 hζV' (F j) (Fi j) (Ft j) (Fit j) i t (hFit j) (hFt j)
  let HW0 := mulWeight d hd (matrixField A Rt j + matrixField (derivativeMatrix A hA2 t) R j)
  let HW1 := mulWeight d hd (matrixField Ai Tcorr j + matrixField (derivativeMatrix Ai hAi t) (cutoffCorrection ζ v) j)
  have hw0 := weighted_matrix_tangential_partial A hA2 R Rt d hd t j ht hRt
  have hw1 := weighted_matrix_tangential_partial Ai hAi (cutoffCorrection ζ v) Tcorr d hd t j ht hTc
  refine ⟨HB+HW0+HW1, ?_⟩
  intro φ
  have hbase := hbase φ
  have hw0 := hw0 φ
  have hw1 := hw1 φ
  change valuePair φ (HB+HW0+HW1) + derivativePair φ t
    (cutoffProductDerivative ζ.complexTest.toTest (F j) (Fi j) i +
      mulWeight d hd (matrixField A R j + matrixField Ai (cutoffCorrection ζ v) j)) = 0
  rw [OQ14.Packet05ScalarEnergyIdentity.mulWeight_add]
  simp only [map_add] at hbase hw0 hw1 ⊢
  linear_combination hbase+hw0+hw1

end OQ14.Packet05LocalizedForcingBootstrap
#print axioms OQ14.Packet05LocalizedForcingBootstrap.forcing_first_tangential
#print axioms OQ14.Packet05LocalizedForcingBootstrap.forcing_second_tangential
