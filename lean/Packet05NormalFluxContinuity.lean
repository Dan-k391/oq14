import Packet05CutoffPlateauDerivative
import Packet05ScalarTangentialContinuity
import Packet05GraphFluxTangential

/-! Continuity of the actual graph-normal conserved flux, from the scalar
transmission equation and its two differentiated equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05NormalFluxContinuity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05GraphNormalFluxH1
  OQ14.Packet05GraphFluxTangential OQ14.Packet05DifferentiatedNormalFluxH1
  OQ14.Packet05CutoffPlateauDerivative OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05DifferentiatedScalarEquation OQ14.Packet05CurlSourceH1
  OQ14.Packet05LocalizedAnisotropic OQ14.Packet05LocalDerivative OQ14.Packet05PartialProduct

theorem normal_flux_continuous (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
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
    (hχ2 : ContDiff ℝ 2 χ.function) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact
        (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)) x) =ᵐ[volume] f := by
  let P : L2Vector := fun j => flux A C d hd j-F j
  let DP (i : Fin 3) : L2Vector := fun j =>
    flux A (C1 i) d hd j-differentiatedSource A hA2 C (F1 i) d hd i j
  obtain ⟨D,hD⟩ := conserved_normal_flux_h1 V A hA2 C F (C1 0) (C1 1) (F1 0) (F1 1) d hd hdiv
    (hC1 0 (by decide)) (hC1 1 (by decide)) (hF1 0 (by decide)) (hF1 1 (by decide)) η hηV
  apply cutoff_continuous_of_tangential_h1
    (scaleL2 η.function η.regular.continuous η.compact (P 2)) D hD χ hχ2
  intro i hi j
  have hPi : HasWeakPartial (P 2) (DP i 2) i :=
    graph_flux_tangential_partial A hA2 C (C1 i) F (F1 i) d hd i 2 hi (hC1 i hi) (hF1 i hi)
  have hDi : D i = cutoffProductDerivative η (P 2) (DP i 2) i := by
    apply weak_partial_unique _ _ _ i (hD i)
    exact cutoff_weak_partial η (P 2) (DP i 2) i hPi
  rw [hDi, cutoff_derivative_plateau W hW η χ hηW hχW (P 2) (DP i 2) i]
  have hdivW : HasDivergenceOn W (fun j => flux A C d hd j-F j) 0 :=
    fun φ hφ => hdiv φ (hφ.trans hWV)
  obtain ⟨G,hG⟩ := differentiated_normal_flux_h1 W hW A hA2 hA3 C F (C1 i) (C1 0) (C1 1)
    (C2 i 0) (C2 i 1) (F1 i) (F2 i 0) (F2 i 1) d hd i hi hdivW
    (hC1 i hi) (hC1 0 (by decide)) (hC1 1 (by decide))
    (hC2 i hi 0 (by decide)) (hC2 i hi 1 (by decide))
    (hF1 i hi) (hF2 i hi 0 (by decide)) (hF2 i hi 1 (by decide)) χ hχW
  exact ⟨G j,hG j⟩

end OQ14.Packet05NormalFluxContinuity
#print axioms OQ14.Packet05NormalFluxContinuity.normal_flux_continuous
