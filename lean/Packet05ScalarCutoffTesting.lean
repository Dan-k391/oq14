import Packet05ScalarHermitianTesting
import Packet05ScalarDifferencePartial
import Packet05PartialProduct
import WeakPoynting.Compactness

/-! The actual differentiated divergence equation is tested with the
conjugate of a cutoff times the scalar difference quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarCutoffTesting
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.WeakPower
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05ScalarDifferenceDivergence OQ14.Packet05ScalarDifferencePartial
  OQ14.Packet05PartialProduct OQ14.Packet05ScalarHermitianTesting

def cutoffDerivative (χ : Test) (u : L2Scalar) (G : Fin 3 → L2Scalar)
    (i : Fin 3) : L2Scalar :=
  scaleL2 χ.function χ.regular.continuous χ.compact (G i) +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u

theorem cutoff_compact (χ : Test) (u : L2Scalar) :
    CompactRepresentative (scaleL2 χ.function χ.regular.continuous χ.compact u) := by
  apply WeakCompactness.supported_compact χ.compact.isCompact
  filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact u] with x hx hn
  rw [hx, image_eq_zero_of_nmem_tsupport hn, zero_mul]

theorem differentiated_divergence_cutoff_test (E : L2Vector) (D u : L2Scalar)
    (G : Fin 3 → L2Scalar) (hdiv : HasWeakDivergence E D)
    (hG : ∀ i, HasWeakPartial u (G i) i) (χ : Test) (t : Fin 3) (h : ℝ) :
    scalarProduct (quotient D t h)
      (conjScalar (scaleL2 χ.function χ.regular.continuous χ.compact (quotient u t h))) +
    scalarProduct (quotient (E 0) t h) (conjScalar (cutoffDerivative χ (quotient u t h)
      (fun i => quotient (G i) t h) 0)) +
    scalarProduct (quotient (E 1) t h) (conjScalar (cutoffDerivative χ (quotient u t h)
      (fun i => quotient (G i) t h) 1)) +
    scalarProduct (quotient (E 2) t h) (conjScalar (cutoffDerivative χ (quotient u t h)
      (fun i => quotient (G i) t h) 2)) = 0 := by
  apply weak_divergence_test_compact_h1_conj (quotientVector E t h) (quotient D t h)
    (scaleL2 χ.function χ.regular.continuous χ.compact (quotient u t h))
    (cutoffDerivative χ (quotient u t h) (fun i => quotient (G i) t h))
    (quotient_weak_divergence E D hdiv t h) (cutoff_compact χ _)
  intro i
  exact cutoff_weak_partial χ _ _ i (quotient_weak_partial u (G i) i t (hG i) h)

end OQ14.Packet05ScalarCutoffTesting
#print axioms OQ14.Packet05ScalarCutoffTesting.cutoff_compact
#print axioms OQ14.Packet05ScalarCutoffTesting.differentiated_divergence_cutoff_test
