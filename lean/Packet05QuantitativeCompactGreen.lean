import Packet05GreenRepresentativeBounds
import Packet05QuantitativeCutoffNorms

/-! The actual compact scalar Green potential has quantitative genuine H2
derivatives, with explicit dependence on its source and fixed cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05QuantitativeCompactGreen
open MeasureTheory Metric Set Maxwell WeakCurl WeakPoynting WeakGreen DivCurlCompact
  Packet05LocalGreenRepresentatives Packet05ActualLocalGreenGradient
  Packet05ActualLocalGreenHessian Packet05LocalPartialProduct Packet05LocalizedAnisotropic
  Packet05QuantitativeCutoffRepresentative Packet05QuantitativeCutoffNorms
  Packet05GreenRepresentativeBounds MaxwellCutoffCommutator

theorem quantitative_compact_green (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (ρ : Space → ℂ) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y=0) (χ : Test)
    (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R)
    (a b c P G H : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : ∀ x, ‖χ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (hc' : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c)
    (hP : ‖LocalConvolution.operator (ComplexGreenKernel.phi z)
      (Packet06ComplexScalarKernel.phi_locallyIntegrable z) (R+S)‖ ≤ P)
    (hG : ∀ i, ‖LocalConvolution.operator (fun y => ComplexGreenKernel.phiGradient z y i)
      (ComplexMagneticLocal.gradient_locallyIntegrable z i) (R+S)‖ ≤ G)
    (hH : ∀ i j, ‖LocalConvolution.operator (fun y => Packet06ComplexHessian.hessianDifference z y i j)
      (Packet06ComplexHessian.hessian_locallyIntegrable z i j) (R+S)‖ ≤ H) :
    ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
      (∀ i, HasWeakPartial U (D i) i) ∧
      (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
      (∀ᵐ x ∂volume, U x=χ.function x*KernelConvolution.response (ComplexGreenKernel.phi z) ρ x) ∧
      ‖U‖ ≤ a*P*‖F‖ ∧ (∀ i, ‖D i‖ ≤ (a*G+b*P)*‖F‖) ∧
      ∀ i j, ‖T i j‖ ≤ (a*(1+H)+2*b*G+c*P)*‖F‖ := by
  let u := actualPotentialRepresentative z R S F ρ hF hρ hs
  let g (i : Fin 3) := gradientRepresentative z R S ρ F hρ hs hF i
  let h (i j : Fin 3) := NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
    (Packet05ScalarNewtonEmbedding.scalarSource F i)) j + dynamicHessianRepresentative z R S ρ F hρ hs hF j i
  have hu : ‖u‖ ≤ P*‖F‖ := (response_representative_norm _ ρ
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) R S F hρ hF hs).trans
    (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hg (i : Fin 3) : ‖g i‖ ≤ G*‖F‖ := (response_representative_norm _ ρ
    (ComplexMagneticLocal.gradient_locallyIntegrable z i) R S F hρ hF hs).trans
    (mul_le_mul_of_nonneg_right (hG i) (norm_nonneg _))
  have hh (i j : Fin 3) : ‖h i j‖ ≤ (1+H)*‖F‖ := by
    have hd := (response_representative_norm _ ρ
      (Packet06ComplexHessian.hessian_locallyIntegrable z j i) R S F hρ hF hs).trans
      (mul_le_mul_of_nonneg_right (hH j i) (norm_nonneg _))
    change ‖dynamicHessianRepresentative z R S ρ F hρ hs hF j i‖ ≤ H*‖F‖ at hd
    exact (norm_add_le _ _).trans (by linarith [static_hessian_norm F i j])
  let U := scaleL2 χ.function χ.regular.continuous χ.compact u
  let D := firstArray u g χ
  let T (i j : Fin 3) := firstArray (g i) (h i) χ j + firstArray u g (derivativeCutoff χ hχ2 i) j
  have hD (i : Fin 3) : HasWeakPartial U (D i) i :=
    local_cutoff_weak_partial _ χ hχR u (g i) i (actual_potential_local_gradient z R S F ρ hF hρ hc hs i)
  have hT (i j : Fin 3) : HasWeakPartial (D i) (T i j) j := by
    have hdχ : tsupport (derivativeCutoff χ hχ2 i).function ⊆ ball 0 R :=
      (RegionalMaxwellHelmholtz.partial_tsupport χ.function i).trans hχR
    exact weak_partial_add _ _ _ _ j
      (local_cutoff_weak_partial _ χ hχR (g i) (h i j) j
        (actual_gradient_local_hessian z R S F ρ hF hρ hc hs j i))
      (local_cutoff_weak_partial _ (derivativeCutoff χ hχ2 i) hdχ u (g j) j
        (actual_potential_local_gradient z R S F ρ hF hρ hc hs j))
  refine ⟨U,D,T,hD,hT,?_,?_,?_,?_⟩
  · have huae := ballRepresentative_ae R _ (LocalConvolution.response_memLp_ball _
      (Packet06ComplexScalarKernel.phi_locallyIntegrable z) ρ hρ F hF R S hs)
    filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact u,huae] with x hx hy
    rw [hx]
    by_cases hxR : x ∈ closedBall (0 : Space) R
    · rw [show u x=KernelConvolution.response (ComplexGreenKernel.phi z) ρ x from hy hxR]
    · have hn : x ∉ tsupport χ.function := fun ht => hxR (ball_subset_closedBall (hχR ht))
      have hzero : χ.function x=0 := (not_mem_tsupport_iff_eventuallyEq.mp hn).self_of_nhds
      simp only [hzero,zero_mul]
  · exact (InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact u ha).trans
      ((mul_le_mul_of_nonneg_left hu ha0).trans_eq (by ring))
  · intro i
    have hbound := first_array_norm u g χ a b ha hb i
    have h1 := mul_le_mul_of_nonneg_left (hg i) ha0
    have h2 := mul_le_mul_of_nonneg_left hu hb0
    change ‖firstArray u g χ i‖ ≤ _
    nlinarith
  · intro i j
    have h1 := first_array_norm (g i) (h i) χ a b ha hb j
    have h2 := first_array_norm u g (derivativeCutoff χ hχ2 i) b c (hb i) (hc' i) j
    have h3 := mul_le_mul_of_nonneg_left (hh i j) ha0
    have h4 := mul_le_mul_of_nonneg_left (hg i) hb0
    have h5 := mul_le_mul_of_nonneg_left (hg j) hb0
    have h6 := mul_le_mul_of_nonneg_left hu hc0
    exact (norm_add_le _ _).trans (by nlinarith)

end OQ14.Packet05QuantitativeCompactGreen
#print axioms OQ14.Packet05QuantitativeCompactGreen.quantitative_compact_green
