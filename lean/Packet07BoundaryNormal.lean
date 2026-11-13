import Packet07FixedPhysical

/-! Coordinate-normal preparation for implicit charts at an actual regular boundary. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryNormal
open Filter Set OQ14.Maxwell
open scoped Topology

theorem nonzero_coordinate (L : Space →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i : Fin 3, L (EuclideanSpace.single i 1) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hL
  have he : L.toLinearMap = 0 := by
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, LinearMap.coe_coe, LinearMap.zero_apply] using h i
  exact ContinuousLinearMap.ext (fun x => congrArg (fun q : Space →ₗ[ℝ] ℝ => q x) he)

theorem regular_normal_nearby (F : Space → ℝ) (x : Space)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F x) (hD : fderiv ℝ F x ≠ 0) :
    ∃ i : Fin 3, ∀ᶠ y in 𝓝 x, fderiv ℝ F y (EuclideanSpace.single i 1) ≠ 0 := by
  obtain ⟨i,hi⟩ := nonzero_coordinate (fderiv ℝ F x) hD
  refine ⟨i, ?_⟩
  have hd : ContinuousAt (fun y => fderiv ℝ F y (EuclideanSpace.single i 1)) x := by
    exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.continuousAt.comp
      ((hF.fderiv_right (m := 0) (by simp)).continuousAt))
  exact hd.eventually (eventually_ne_nhds hi)

end OQ14.Packet07BoundaryNormal
#print axioms OQ14.Packet07BoundaryNormal.nonzero_coordinate
#print axioms OQ14.Packet07BoundaryNormal.regular_normal_nearby
