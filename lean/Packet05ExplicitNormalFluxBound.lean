import Packet05NormalFluxArrays
import Packet05QuantitativeCutoffNorms

/-! Quantitative normal-flux continuity with explicit derivative arrays. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05ExplicitNormalFluxBound
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05ScalarDielectricFlux Packet05PartialProduct
  Packet05NormalFluxArrays Packet05LocalizedAnisotropic MaxwellCutoffCommutator

theorem normal_flux_explicit_bound (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
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
    (hηW : ∀ x ∈ W, η.function x = 1) (hχW : tsupport χ.function ⊆ W) (hχ2 : ContDiff ℝ 2 χ.function) (a b c : ℝ)
    (ha : ∀ x, ‖χ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact
        (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)) x) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((a+3*b+6*c)*‖scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)‖ +
         (a+2*b)*(∑ i : Fin 3, ‖firstFluxArray A hA2 C F C1 F1 d hd η i‖) +
         ∑ i : Fin 2, ∑ j : Fin 3, ‖secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i.castSucc j‖) := by
  obtain ⟨hD,hV⟩ := normal_flux_arrays V W hW hWV A hA2 hA3 C F C1 F1 C2 F2 d hd hdiv
    hC1 hF1 hC2 hF2 η χ hηV hηW hχW
  exact Packet05QuantitativeCutoffNorms.cutoff_original_derivatives
    (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2))
    (firstFluxArray A hA2 C F C1 F1 d hd η) hD χ hχ2
    (secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ) hV a b c ha hb hc

end OQ14.Packet05ExplicitNormalFluxBound
#print axioms OQ14.Packet05ExplicitNormalFluxBound.normal_flux_explicit_bound
