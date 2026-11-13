import Packet05RegionalDivergence

/-! A global weak divergence whose source vanishes on an open region induces
the homogeneous regional divergence equation there. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05DivergenceZeroRegion
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence

theorem global_divergence_zero_on (V : Set Space) (P : L2Vector) (D : L2Scalar)
    (hdiv : HasWeakDivergence P D) (hD : ∀ᵐ x ∂volume, x ∈ V → D x=0) :
    HasDivergenceOn V P 0 := by
  intro φ hφ
  have h := global_divergence_on V P D hdiv φ hφ
  have hz : valuePair φ D = 0 := by
    simp only [valuePair,testPair_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [hD] with x hx
    by_cases hxV : x ∈ V
    · simp [hx hxV]
    · have hn : x ∉ tsupport φ.function := fun hh => hxV (hφ hh)
      simp [image_eq_zero_of_nmem_tsupport hn]
  simpa [hz] using h

end OQ14.Packet05DivergenceZeroRegion
#print axioms OQ14.Packet05DivergenceZeroRegion.global_divergence_zero_on
