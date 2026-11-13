import Packet05RegionalDivergence
import Packet05GraphFluxExtension
import Packet05ScalarDielectricFlux

/-! Regional divergence depends only on the a.e. values of its flux and
source inside the test region. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalDivergenceCongruence
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05TensorCommutator
  OQ14.Packet05GraphFluxExtension OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux

theorem divergence_on_of_ae_eq (V : Set Space) (E F : L2Vector) (D : L2Scalar)
    (hE : HasDivergenceOn V E D)
    (hEF : ∀ j, ∀ᵐ x ∂volume, x ∈ V → F j x = E j x) : HasDivergenceOn V F D := by
  intro φ hφV
  have he (j : Fin 3) : derivativePair φ j (F j) = derivativePair φ j (E j) := by
    simp only [derivativePair, testPair_integral]
    apply integral_congr_ae
    filter_upwards [hEF j] with x hx
    by_cases hV : x ∈ V
    · rw [hx hV]
    · have hnot : x ∉ tsupport φ.function := fun h => hV (hφV h)
      have hz : dcoord φ.function x j = 0 := by simp [dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
      simp [hz]
  rw [he 0,he 1,he 2]
  exact hE φ hφV

theorem flux_local_ae_eq (V : Set Space) (A : Fin 3 → Fin 3 → Test)
    (C G : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hCG : ∀ j, ∀ᵐ x ∂volume, x ∈ V → G j x = C j x) (j : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ V → flux A G d hd j x = flux A C d hd j x := by
  have he : ∀ᵐ x ∂volume, ∀ k, x ∈ V → G k x = C k x := ae_all_iff.mpr hCG
  filter_upwards [he, mulWeight_ae d hd (matrixField A G j), mulWeight_ae d hd (matrixField A C j),
    matrixField_ae A G j, matrixField_ae A C j] with x he hwg hwc hag hac hx
  change mulWeight d hd (matrixField A G j) x = mulWeight d hd (matrixField A C j) x
  rw [hwg,hwc,hag,hac]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [he k hx]

end OQ14.Packet05RegionalDivergenceCongruence
#print axioms OQ14.Packet05RegionalDivergenceCongruence.divergence_on_of_ae_eq
#print axioms OQ14.Packet05RegionalDivergenceCongruence.flux_local_ae_eq
