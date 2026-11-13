import Packet05RegionalScalarLocalization
import Packet05WeightedMatrixDerivative
import Packet05CurlSourceH1

/-! The localized scalar forcing has its actual tangential weak derivative,
including both matrix and cutoff commutators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalizedScalarForcingDerivative
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarSquareCutoff
  OQ14.Packet05RegionalScalarLocalization OQ14.MaxwellCutoffCommutator
  OQ14.Packet05CurlSourceH1 OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative

theorem localized_forcing_tangential_derivative (V : Set Space) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (v Dv : L2Scalar) (F DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (t : Fin 3) (ht : t ≠ 2)
    (hv : HasPartialOn V v Dv t) (hF : ∀ j, HasPartialOn V (F j) (DF j) t)
    (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function) (hζV : tsupport ζ.function ⊆ V) :
    ∃ DForce : L2Vector, ∀ j, HasWeakPartial (localizedForcing ζ A v F d hd j) (DForce j) t := by
  have hζV' : tsupport ζ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hζV
  have hζc2 : ContDiff ℝ 2 ζ.complexTest.function := Complex.ofRealCLM.contDiff.comp hζ2
  let Dcorr : L2Vector := fun j => cutoffProductDerivative
    (derivativeCutoff ζ.complexTest.toTest hζc2 j) v Dv t
  have hcorr (j : Fin 3) : HasWeakPartial (cutoffCorrection ζ v j) (Dcorr j) t := by
    have hsup : tsupport (derivativeCutoff ζ.complexTest.toTest hζc2 j).function ⊆ V :=
      (RegionalMaxwellHelmholtz.partial_tsupport ζ.complexTest.function j).trans hζV'
    exact local_cutoff_weak_partial V (derivativeCutoff ζ.complexTest.toTest hζc2 j) hsup v Dv t hv
  let DForce : L2Vector := fun j =>
    (cutoffProductDerivative ζ.complexTest.toTest (F j) (DF j) t) +
      mulWeight d hd (matrixField A Dcorr j + matrixField (derivativeMatrix A hA t) (cutoffCorrection ζ v) j)
  refine ⟨DForce,?_⟩
  intro j
  have hf := local_cutoff_weak_partial V ζ.complexTest.toTest hζV' (F j) (DF j) t (hF j)
  have hw := weighted_matrix_tangential_partial A hA (cutoffCorrection ζ v) Dcorr d hd t j ht hcorr
  intro φ
  have hf := hf φ
  have hw := hw φ
  change valuePair φ (_ + _) + derivativePair φ t (_ + _) = 0
  simp only [map_add, cutoffProductDerivative, cutVector, flux] at hf ⊢
  linear_combination hf + hw

end OQ14.Packet05LocalizedScalarForcingDerivative
#print axioms OQ14.Packet05LocalizedScalarForcingDerivative.localized_forcing_tangential_derivative
