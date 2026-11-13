import Packet05CurlCommutation

/-! Distributional partial derivatives commute with weak divergence, with
no interface or constitutive assumptions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DivergenceCommutation
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.LocalRegularity OQ14.Packet05DivergenceUpgrade
  OQ14.Packet05CurlCommutation

theorem partial_commutes_weakDivergence (E G : L2Vector) (D J : L2Scalar) (i : Fin 3)
    (hdiv : HasWeakDivergence E D) (hE : ∀ j, HasWeakPartial (E j) (G j) i)
    (hD : HasWeakPartial D J i) : HasWeakDivergence G J := by
  apply smooth_divergence_to_weak
  intro φ hφ
  let ψ := partialTest φ hφ i
  have hdivψ := hdiv ψ
  have hDφ := hD φ
  have hE0 := hE 0 (partialTest φ hφ 0)
  have hE1 := hE 1 (partialTest φ hφ 1)
  have hE2 := hE 2 (partialTest φ hφ 2)
  have h0 := derivativePair_partial_comm φ hφ i 0 (E 0)
  have h1 := derivativePair_partial_comm φ hφ i 1 (E 1)
  have h2 := derivativePair_partial_comm φ hφ i 2 (E 2)
  change valuePair ψ D + derivativePair ψ 0 (E 0) + derivativePair ψ 1 (E 1) + derivativePair ψ 2 (E 2) = 0 at hdivψ
  rw [h0,h1,h2] at hdivψ
  change valuePair φ J + valuePair ψ D = 0 at hDφ
  change derivativePair φ 0 (G 0) + derivativePair (partialTest φ hφ 0) i (E 0) = 0 at hE0
  change derivativePair φ 1 (G 1) + derivativePair (partialTest φ hφ 1) i (E 1) = 0 at hE1
  change derivativePair φ 2 (G 2) + derivativePair (partialTest φ hφ 2) i (E 2) = 0 at hE2
  linear_combination -hdivψ + hDφ + hE0 + hE1 + hE2

end OQ14.Packet05DivergenceCommutation
#print axioms OQ14.Packet05DivergenceCommutation.partial_commutes_weakDivergence
