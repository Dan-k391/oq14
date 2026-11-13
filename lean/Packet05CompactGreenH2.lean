import Packet05LocalGreenGradient
import Packet05LocalPartialProduct
import Packet05LocalizedAnisotropic

/-! Compact cutoffs of the actual complex Green potential possess all first
and second weak L² derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05CompactGreenH2
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05LocalizedAnisotropic
  OQ14.Packet05LocalGreenRepresentatives OQ14.Packet05LocalGreenGradient
  OQ14.Packet05LocalGreenHessian OQ14.Packet05ComplexCorrectionRegularity
  OQ14.Packet05PartialProduct OQ14.MaxwellCutoffCommutator OQ14.KernelConvolution

theorem compact_green_h2 (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hc : HasCompactSupport (F : Space → ℂ))
    (hs : ∀ y, y ∉ closedBall 0 S → F y = 0) (χ : Test)
    (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R) :
    ∃ U : L2Scalar, ∃ G : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ j, HasWeakPartial U (G j) j) ∧
      (∀ i j, HasWeakPartial (G i) (H i j) j) ∧
      (∀ᵐ x ∂volume, U x = χ.function x * response (ComplexGreenKernel.phi z) F x) := by
  let u := potentialRepresentative z R S F hF hs
  let g (i : Fin 3) := gradientRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i
  let h (i j : Fin 3) := NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
    (Packet05ScalarNewtonEmbedding.scalarSource F i)) j +
    dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) j i
  let U := scaleL2 χ.function χ.regular.continuous χ.compact u
  let G (i : Fin 3) := scaleL2 χ.function χ.regular.continuous χ.compact (g i) +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u
  have hg (i : Fin 3) : HasWeakPartial U (G i) i :=
    local_cutoff_weak_partial _ χ hχR u (g i) i (potential_local_gradient z R S F hF hc hs i)
  have hsecond (i j : Fin 3) : ∃ v : L2Scalar, HasWeakPartial (G i) v j := by
    let dχ := derivativeCutoff χ hχ2 i
    have hdχ : tsupport dχ.function ⊆ ball 0 R :=
      (RegionalMaxwellHelmholtz.partial_tsupport χ.function i).trans hχR
    have h1 := local_cutoff_weak_partial _ χ hχR (g i) (h i j) j
      (gradient_local_hessian z R S F hF hc hs j i)
    have h2 := local_cutoff_weak_partial _ dχ hdχ u (g j) j
      (potential_local_gradient z R S F hF hc hs j)
    refine ⟨_, weak_partial_add _ _ _ _ j h1 h2⟩
  classical
  let H (i j : Fin 3) := Classical.choose (hsecond i j)
  refine ⟨U, G, H, hg, (fun i j => Classical.choose_spec (hsecond i j)), ?_⟩
  have hu := ballRepresentative_ae R _ (LocalConvolution.response_memLp_ball _
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) F hF F
    (Filter.EventuallyEq.rfl) R S hs)
  filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact u, hu] with x hx hy
  rw [hx]
  by_cases hR : x ∈ closedBall 0 R
  · rw [show u x = response (ComplexGreenKernel.phi z) F x from hy hR]
  · have hnot : x ∉ tsupport χ.function := fun hx => hR (ball_subset_closedBall (hχR hx))
    have hz : χ.function x = 0 := (not_mem_tsupport_iff_eventuallyEq.mp hnot).self_of_nhds
    simp [hz]

end OQ14.Packet05CompactGreenH2
#print axioms OQ14.Packet05CompactGreenH2.compact_green_h2
