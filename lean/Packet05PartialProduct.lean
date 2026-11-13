import Packet05CurlCommutation

/-! The cutoff product rule for a single genuine weak L² partial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PartialProduct
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact

theorem cutoff_weak_partial (χ : Test)
    (u D : L2Scalar) (i : Fin 3) (hD : HasWeakPartial u D i) :
    HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact u)
      (scaleL2 χ.function χ.regular.continuous χ.compact D +
        scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
          (χ.compact.fderiv_apply ℝ (basis i)) u) i := by
  intro φ
  have hh := hD (smoothProductTest χ φ.function φ.regular)
  have hval : valuePair (smoothProductTest χ φ.function φ.regular) D =
      valuePair φ (scaleL2 χ.function χ.regular.continuous χ.compact D) := by
    simp only [valuePair, testPair_integral]
    apply integral_congr_ae
    filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact D] with x hx
    rw [hx]
    simp [smoothProductTest]
    ring
  have hder : derivativePair (smoothProductTest χ φ.function φ.regular) i u =
      derivativePair φ i (scaleL2 χ.function χ.regular.continuous χ.compact u) +
      valuePair φ (scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
        (χ.compact.fderiv_apply ℝ (basis i)) u) := by
    rw [derivativePair_smooth_product]
    simp only [derivativePair, valuePair, scalarProduct_scale_smooth]
    simp only [testPair_integral]
    congr 1
    · apply integral_congr_ae
      filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact u] with x hu
      rw [hu]
      ring
    · apply integral_congr_ae
      filter_upwards [scaleL2_ae (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
        (χ.compact.fderiv_apply ℝ (basis i)) u] with x hd
      rw [hd]
      ring
  rw [hval, hder] at hh
  simp only [map_add]
  linear_combination hh

end OQ14.Packet05PartialProduct
#print axioms OQ14.Packet05PartialProduct.cutoff_weak_partial
