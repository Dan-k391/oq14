import Packet05ActualLocalGreenGradient
import Packet05LocalPartialProduct
import Packet05LocalizedAnisotropic

/-! Compact cutoffs of the actual complex Green potential possess all first
and second weak L² derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualCompactGreenH2
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05LocalizedAnisotropic
  OQ14.Packet05LocalGreenRepresentatives OQ14.Packet05ActualLocalGreenGradient
  OQ14.Packet05ActualLocalGreenHessian OQ14.Packet05ComplexCorrectionRegularity
  OQ14.Packet05PartialProduct OQ14.MaxwellCutoffCommutator OQ14.KernelConvolution

theorem actual_compact_green_h2 (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (ρ : Space → ℂ) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (χ : Test)
    (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R) :
    ∃ U : L2Scalar, ∃ G : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ j, HasWeakPartial U (G j) j) ∧
      (∀ i j, HasWeakPartial (G i) (H i j) j) ∧
      (∀ᵐ x ∂volume, U x = χ.function x * response (ComplexGreenKernel.phi z) ρ x) := by
  let u := actualPotentialRepresentative z R S F ρ hF hρ hs
  let g (i : Fin 3) := gradientRepresentative z R S ρ F hρ hs hF i
  let h (i j : Fin 3) := NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
    (Packet05ScalarNewtonEmbedding.scalarSource F i)) j +
    dynamicHessianRepresentative z R S ρ F hρ hs hF j i
  let U := scaleL2 χ.function χ.regular.continuous χ.compact u
  let G (i : Fin 3) := scaleL2 χ.function χ.regular.continuous χ.compact (g i) +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u
  have hg (i : Fin 3) : HasWeakPartial U (G i) i :=
    local_cutoff_weak_partial _ χ hχR u (g i) i (actual_potential_local_gradient z R S F ρ hF hρ hc hs i)
  have hsecond (i j : Fin 3) : ∃ v : L2Scalar, HasWeakPartial (G i) v j := by
    let dχ := derivativeCutoff χ hχ2 i
    have hdχ : tsupport dχ.function ⊆ ball 0 R :=
      (RegionalMaxwellHelmholtz.partial_tsupport χ.function i).trans hχR
    have h1 := local_cutoff_weak_partial _ χ hχR (g i) (h i j) j
      (actual_gradient_local_hessian z R S F ρ hF hρ hc hs j i)
    have h2 := local_cutoff_weak_partial _ dχ hdχ u (g j) j
      (actual_potential_local_gradient z R S F ρ hF hρ hc hs j)
    refine ⟨_, weak_partial_add _ _ _ _ j h1 h2⟩
  classical
  let H (i j : Fin 3) := Classical.choose (hsecond i j)
  refine ⟨U, G, H, hg, (fun i j => Classical.choose_spec (hsecond i j)), ?_⟩
  have hu := ballRepresentative_ae R _ (LocalConvolution.response_memLp_ball _
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) ρ hρ F
    hF R S hs)
  filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact u, hu] with x hx hy
  rw [hx]
  by_cases hR : x ∈ closedBall 0 R
  · rw [show u x = response (ComplexGreenKernel.phi z) ρ x from hy hR]
  · have hnot : x ∉ tsupport χ.function := fun hx => hR (ball_subset_closedBall (hχR hx))
    have hz : χ.function x = 0 := (not_mem_tsupport_iff_eventuallyEq.mp hnot).self_of_nhds
    simp [hz]

end OQ14.Packet05ActualCompactGreenH2
#print axioms OQ14.Packet05ActualCompactGreenH2.actual_compact_green_h2
