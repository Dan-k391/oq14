import Packet05NormalFluxOriginalBound

/-! Fixed-coefficient numerical envelopes for the explicit flux bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05NormalFluxEnvelope
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05NormalFluxDataBounds Packet05NormalFluxOriginalBound

theorem size_le_three (C : L2Vector) (L : ℝ) (h : ∀ j, ‖C j‖ ≤ L) : size C ≤ 3*L := by
  dsimp [size]
  linarith [h 0,h 1,h 2]

theorem first_bound_envelope (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector)
    (d a b r s L : ℝ) (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hC : ∀ j, ‖C j‖ ≤ L) (hF : ∀ j, ‖F j‖ ≤ L)
    (hC1 : ∀ i j, ‖C1 i j‖ ≤ L) (hF1 : ∀ i j, ‖F1 i j‖ ≤ L) :
    firstBound C F C1 F1 d a b r s ≤
      (r*(2*((1+d)*(3*a+3*b)+3))+s*((1+d)*3*a+1))*L := by
  have hc := size_le_three C L hC
  have hc0 := size_le_three (C1 0) L (hC1 0)
  have hc1 := size_le_three (C1 1) L (hC1 1)
  have hf0 := size_le_three (F1 0) L (hF1 0)
  have hf1 := size_le_three (F1 1) L (hF1 1)
  have h0 : 0 ≤ 1+d := by linarith
  have hA := mul_le_mul_of_nonneg_left hc ha
  have hB := mul_le_mul_of_nonneg_left hc hb
  have hC0 := mul_le_mul_of_nonneg_left hc0 ha
  have hC1 := mul_le_mul_of_nonneg_left hc1 ha
  have hF0 := hF 2
  have hX0 := mul_le_mul_of_nonneg_left (add_le_add hC0 hB) h0
  have hX1 := mul_le_mul_of_nonneg_left (add_le_add hC1 hB) h0
  have hX2 := mul_le_mul_of_nonneg_left hA h0
  have hR := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hX0 hf0) (add_le_add hX1 hf1)) hr
  have hS := mul_le_mul_of_nonneg_left (add_le_add hX2 hF0) hs
  unfold firstBound
  nlinarith only [hR,hS]

theorem second_bound_envelope (C : L2Vector) (C1 F1 : Fin 3 → L2Vector)
    (C2 F2 : Fin 3 → Fin 3 → L2Vector) (d a b c p q L : ℝ)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hC : ∀ j, ‖C j‖ ≤ L) (hC1 : ∀ i j, ‖C1 i j‖ ≤ L)
    (hF1 : ∀ i j, ‖F1 i j‖ ≤ L) (hC2 : ∀ i t j, ‖C2 i t j‖ ≤ L)
    (hF2 : ∀ i t j, ‖F2 i t j‖ ≤ L) (i : Fin 3) :
    secondBound C C1 F1 C2 F2 d a b c p q i ≤
      (p*(2*((1+d)*(3*a+3*b)+3+(1+d)*(3*b+3*c)))+
       q*((1+d)*3*a+1+(1+d)*3*b))*L := by
  have hC0 := size_le_three C L hC
  have hCi := size_le_three (C1 i) L (hC1 i)
  have hC10 := size_le_three (C1 0) L (hC1 0)
  have hC11 := size_le_three (C1 1) L (hC1 1)
  have hC20 := size_le_three (C2 i 0) L (hC2 i 0)
  have hC21 := size_le_three (C2 i 1) L (hC2 i 1)
  have hF20 := size_le_three (F2 i 0) L (hF2 i 0)
  have hF21 := size_le_three (F2 i 1) L (hF2 i 1)
  have h0 : 0 ≤ 1+d := by linarith
  have h1 := mul_le_mul_of_nonneg_left hC20 ha
  have h2 := mul_le_mul_of_nonneg_left hC21 ha
  have h3 := mul_le_mul_of_nonneg_left hCi hb
  have h4 := mul_le_mul_of_nonneg_left hC10 hb
  have h5 := mul_le_mul_of_nonneg_left hC11 hb
  have h6 := mul_le_mul_of_nonneg_left hC0 hc
  have h7 := mul_le_mul_of_nonneg_left hCi ha
  have h8 := mul_le_mul_of_nonneg_left hC0 hb
  have h9 := mul_le_mul_of_nonneg_left (add_le_add h1 h3) h0
  have h10 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) h0
  have h11 := mul_le_mul_of_nonneg_left (add_le_add h4 h6) h0
  have h12 := mul_le_mul_of_nonneg_left (add_le_add h5 h6) h0
  have h13 := mul_le_mul_of_nonneg_left h7 h0
  have h14 := mul_le_mul_of_nonneg_left h8 h0
  have hR := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h9 hF20) h11) (add_le_add (add_le_add h10 hF21) h12)) hp
  have hS := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h13 (hF1 i 2)) h14) hq
  unfold secondBound
  nlinarith only [hR,hS]


theorem total_flux_envelope (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector)
    (C2 F2 : Fin 3 → Fin 3 → L2Vector) (d a b c r s p q t L : ℝ)
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hC : ∀ j, ‖C j‖ ≤ L) (hF : ∀ j, ‖F j‖ ≤ L)
    (hC1 : ∀ i j, ‖C1 i j‖ ≤ L) (hF1 : ∀ i j, ‖F1 i j‖ ≤ L)
    (hC2 : ∀ i t j, ‖C2 i t j‖ ≤ L) (hF2 : ∀ i t j, ‖F2 i t j‖ ≤ L) :
    (p+3*q+6*t)*r*((1+d)*a*size C+‖F 2‖) +
      (p+2*q)*3*firstBound C F C1 F1 d a b r s +
      ∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc ≤
    ((p+3*q+6*t)*r*((1+d)*3*a+1) +
      (p+2*q)*3*(r*(2*((1+d)*(3*a+3*b)+3))+s*((1+d)*3*a+1)) +
      6*(p*(2*((1+d)*(3*a+3*b)+3+(1+d)*(3*b+3*c)))+
         q*((1+d)*3*a+1+(1+d)*3*b)))*L := by
  have h0 : 0 ≤ 1+d := by linarith
  have hC0 := size_le_three C L hC
  have hC1' := mul_le_mul_of_nonneg_left hC0 ha
  have hC2' := mul_le_mul_of_nonneg_left hC1' h0
  have hF2' := hF 2
  have hbase := add_le_add hC2' hF2'
  have hfirst := first_bound_envelope C F C1 F1 d a b r s L hd ha hb hr hs hC hF hC1 hF1
  have hsecond (i : Fin 2) := second_bound_envelope C C1 F1 C2 F2 d a b c p q L hd ha hb hc hp hq hC hC1 hF1 hC2 hF2 i.castSucc
  have hsecondSum : (∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc) ≤
      6*((p*(2*((1+d)*(3*a+3*b)+3+(1+d)*(3*b+3*c)))+
         q*((1+d)*3*a+1+(1+d)*3*b))*L) := by
    simp only [Fin.sum_univ_two,Fin.sum_univ_three]
    linarith [hsecond 0,hsecond 1]
  have hR := mul_le_mul_of_nonneg_left hbase (mul_nonneg (by linarith : 0 ≤ p+3*q+6*t) hr)
  have hS := mul_le_mul_of_nonneg_left hfirst (by linarith : 0 ≤ (p+2*q)*3)
  nlinarith only [hR,hS,hsecondSum]
end OQ14.Packet05NormalFluxEnvelope
#print axioms OQ14.Packet05NormalFluxEnvelope.size_le_three
#print axioms OQ14.Packet05NormalFluxEnvelope.first_bound_envelope
#print axioms OQ14.Packet05NormalFluxEnvelope.second_bound_envelope
#print axioms OQ14.Packet05NormalFluxEnvelope.total_flux_envelope
