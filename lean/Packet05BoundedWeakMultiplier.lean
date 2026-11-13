import Packet05ModeCorrectionH2
import Packet05GraphH1Pullback

/-! Product rule for bounded smooth chart coefficients acting on genuine L²
weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05BoundedWeakMultiplier
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact

def boundedMultiply (a : Space → ℂ) (ha : MemLp a ⊤ volume) (u : L2Scalar) : L2Scalar :=
  ((Lp.memLp u).mul' ha).toLp (fun x => a x * u x)

theorem boundedMultiply_ae (a : Space → ℂ) (ha : MemLp a ⊤ volume) (u : L2Scalar) :
    (fun x => boundedMultiply a ha u x) =ᵐ[volume] fun x => a x * u x :=
  ((Lp.memLp u).mul' ha).coeFn_toLp

theorem bounded_multiplier_weak_partial (a : Space → ℂ) (ha : ContDiff ℝ 1 a)
    (hbound : MemLp a ⊤ volume) (i : Fin 3)
    (hdi : MemLp (fun x => dcoord a x i) ⊤ volume)
    (u D : L2Scalar) (hD : HasWeakPartial u D i) :
    HasWeakPartial (boundedMultiply a hbound u)
      (boundedMultiply a hbound D + boundedMultiply (fun x => dcoord a x i) hdi u) i := by
  intro φ
  have hh := hD (smoothProductTest φ a ha)
  have hv : valuePair (smoothProductTest φ a ha) D =
      valuePair φ (boundedMultiply a hbound D) := by
    simp only [valuePair, testPair_integral]
    apply integral_congr_ae
    filter_upwards [boundedMultiply_ae a hbound D] with x hx
    rw [hx]
    simp [smoothProductTest]
    ring
  have hd : derivativePair (smoothProductTest φ a ha) i u =
      valuePair φ (boundedMultiply (fun x => dcoord a x i) hdi u) +
      derivativePair φ i (boundedMultiply a hbound u) := by
    rw [derivativePair_smooth_product]
    simp only [derivativePair, valuePair, testPair_integral]
    congr 1
    · apply integral_congr_ae
      filter_upwards [boundedMultiply_ae (fun x => dcoord a x i) hdi u] with x hx
      rw [hx]
      ring
    · apply integral_congr_ae
      filter_upwards [boundedMultiply_ae a hbound u] with x hx
      rw [hx]
      ring
  rw [hv, hd] at hh
  simp only [map_add]
  linear_combination hh

end OQ14.Packet05BoundedWeakMultiplier
#print axioms OQ14.Packet05BoundedWeakMultiplier.boundedMultiply_ae
#print axioms OQ14.Packet05BoundedWeakMultiplier.bounded_multiplier_weak_partial
