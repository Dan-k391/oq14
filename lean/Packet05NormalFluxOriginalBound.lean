import Packet05FirstNormalFluxDataBound
import Packet05ExplicitNormalFluxBound

/-! A normal-flux representative bounded by scalar transmission data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet05NormalFluxOriginalBound
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05ScalarDielectricFlux Packet05PartialProduct
  Packet05NormalFluxArrays Packet05NormalFluxNorms Packet05NormalFluxDataBounds
  Packet05FirstNormalFluxDataBound Packet05MatrixWeakDerivative MaxwellCutoffCommutator

def firstBound (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (d a b r s : ℝ) : ℝ :=
  r*((1+d)*(a*size (C1 0)+b*size C)+size (F1 0)+
     ((1+d)*(a*size (C1 1)+b*size C)+size (F1 1)))+
  s*((1+d)*a*size C+‖F 2‖)

def secondBound (C : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d a b c r s : ℝ) (i : Fin 3) : ℝ :=
  r*((1+d)*(a*size (C2 i 0)+b*size (C1 i))+size (F2 i 0)+(1+d)*(b*size (C1 0)+c*size C)+
     ((1+d)*(a*size (C2 i 1)+b*size (C1 i))+size (F2 i 1)+(1+d)*(b*size (C1 1)+c*size C)))+
  s*((1+d)*a*size (C1 i)+‖F1 i 2‖+(1+d)*b*size C)

theorem normal_flux_original_bound (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (C j) (C1 i j) i)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hC2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (η χ : Test) (hηV : tsupport η.function ⊆ V)
    (hηW : ∀ x ∈ W, η.function x = 1) (hχW : tsupport χ.function ⊆ W)
    (hχ2 : ContDiff ℝ 2 χ.function) (a b c r s p q t : ℝ)
    (ha : ∀ i j x, ‖(A i j).function x‖ ≤ a)
    (hb : ∀ i j k x, ‖dcoord (A i j).function x k‖ ≤ b)
    (hc : ∀ i j k l x, ‖dcoord (derivativeMatrix A hA2 k i j).function x l‖ ≤ c)
    (hr : ∀ x, ‖η.function x‖ ≤ r) (hs : ∀ i x, ‖dcoord η.function x i‖ ≤ s)
    (hp : ∀ x, ‖χ.function x‖ ≤ p) (hq : ∀ i x, ‖dcoord χ.function x i‖ ≤ q)
    (ht : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ t) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact
        (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)) x) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((p+3*q+6*t)*r*((1+d)*a*size C+‖F 2‖) +
         (p+2*q)*3*firstBound C F C1 F1 d a b r s +
         ∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc) := by
  obtain ⟨f,hf,he,hbound⟩ := Packet05ExplicitNormalFluxBound.normal_flux_explicit_bound
    V W hW hWV A hA2 hA3 C F C1 F1 C2 F2 d hd hdiv hC1 hF1 hC2 hF2
    η χ hηV hηW hχW hχ2 p q t hp hq ht
  refine ⟨f,hf,he,?_⟩
  intro x
  apply (hbound x).trans
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp 0)
  have hq0 : 0 ≤ q := (norm_nonneg _).trans (hq 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans (ht 0 0 0)
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr 0)
  have hU := InteriorTestDensity.scaleL2_norm_le η.function η.regular.continuous η.compact (flux A C d hd 2-F 2) hr
  have hflux := flux_norm A C F d hd 2 a ha
  have hD (i : Fin 3) : ‖firstFluxArray A hA2 C F C1 F1 d hd η i‖ ≤ firstBound C F C1 F1 d a b r s := by
    simpa [firstBound] using first_flux_original_bound A hA2 C F C1 F1 d hd η i a b r s ha hb hr hs
  have hV (i : Fin 2) (j : Fin 3) : ‖secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i.castSucc j‖ ≤ secondBound C C1 F1 C2 F2 d a b c p q i.castSucc := by
    simpa [secondBound,size] using second_flux_original_bound A hA2 hA3 C F C1 F1 C2 F2 d hd χ i.castSucc j a b c p q ha hb (fun p q t x => hc p q i.castSucc t x) hp hq
  have hsumD : (∑ i : Fin 3, ‖firstFluxArray A hA2 C F C1 F1 d hd η i‖) ≤ 3*firstBound C F C1 F1 d a b r s := by
    simp only [Fin.sum_univ_three]
    linarith [hD 0,hD 1,hD 2]
  have hsumV : (∑ i : Fin 2, ∑ j : Fin 3, ‖secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i.castSucc j‖) ≤
      ∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hV i j))
  apply mul_le_mul_of_nonneg_left _ (by unfold Packet05ExplicitAnisotropicBound.universalConstant; positivity)
  have hU' := hU.trans (mul_le_mul_of_nonneg_left hflux hr0)
  have h1 := mul_le_mul_of_nonneg_left hU' (by linarith : 0 ≤ p+3*q+6*t)
  have h2 := mul_le_mul_of_nonneg_left hsumD (by linarith : 0 ≤ p+2*q)
  dsimp [size] at h1 ⊢
  nlinarith only [h1,h2,hsumV]

end OQ14.Packet05NormalFluxOriginalBound
#print axioms OQ14.Packet05NormalFluxOriginalBound.normal_flux_original_bound
