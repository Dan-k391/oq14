import Packet05NormalFluxEnvelope

/-! A uniform normal-flux constant for a fixed chart and scalar-data ceiling. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05NormalFluxUniformCeiling
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05NormalFluxDataBounds Packet05NormalFluxOriginalBound Packet05NormalFluxEnvelope

def coefficient (d a b c r s p q t : ℝ) : ℝ :=
  Packet05ExplicitAnisotropicBound.universalConstant *
    ((p+3*q+6*t)*r*((1+d)*3*a+1) +
      (p+2*q)*3*(r*(2*((1+d)*(3*a+3*b)+3))+s*((1+d)*3*a+1)) +
      6*(p*(2*((1+d)*(3*a+3*b)+3+(1+d)*(3*b+3*c)))+
         q*((1+d)*3*a+1+(1+d)*3*b)))

theorem uniform_flux_ceiling (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector)
    (C2 F2 : Fin 3 → Fin 3 → L2Vector) (d a b c r s p q t L : ℝ)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hC : ∀ j, ‖C j‖ ≤ L) (hF : ∀ j, ‖F j‖ ≤ L)
    (hC1 : ∀ i j, ‖C1 i j‖ ≤ L) (hF1 : ∀ i j, ‖F1 i j‖ ≤ L)
    (hC2 : ∀ i t j, ‖C2 i t j‖ ≤ L) (hF2 : ∀ i t j, ‖F2 i t j‖ ≤ L) :
    Packet05ExplicitAnisotropicBound.universalConstant *
      ((p+3*q+6*t)*r*((1+d)*a*size C+‖F 2‖) +
        (p+2*q)*3*firstBound C F C1 F1 d a b r s +
        ∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc) ≤
    coefficient d a b c r s p q t * L := by
  have h := total_flux_envelope C F C1 F1 C2 F2 d a b c r s p q t L
    hd ha hb hc hr hs hp hq ht hC hF hC1 hF1 hC2 hF2
  have hu : 0 ≤ Packet05ExplicitAnisotropicBound.universalConstant := by
    unfold Packet05ExplicitAnisotropicBound.universalConstant
    positivity
  have hm := mul_le_mul_of_nonneg_left h hu
  simpa [coefficient,mul_assoc] using hm

end OQ14.Packet05NormalFluxUniformCeiling
#print axioms OQ14.Packet05NormalFluxUniformCeiling.uniform_flux_ceiling
