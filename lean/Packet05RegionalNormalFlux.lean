import Packet05RegionalDivergence

/-! Recover the normal weak derivative of a flux component from its
regional divergence and two tangential partials. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05RegionalNormalFlux
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence

theorem regional_normal_flux_partial (V : Set Space) (P : L2Vector) (D A B : L2Scalar)
    (hdiv : HasDivergenceOn V P D)
    (h0 : HasPartialOn V (P 0) A 0) (h1 : HasPartialOn V (P 1) B 1) :
    HasPartialOn V (P 2) (D-A-B) 2 := by
  intro φ hφ
  have hd := hdiv φ hφ
  have h0 := h0 φ hφ
  have h1 := h1 φ hφ
  simp only [map_sub]
  linear_combination hd - h0 - h1

end OQ14.Packet05RegionalNormalFlux
#print axioms OQ14.Packet05RegionalNormalFlux.regional_normal_flux_partial
