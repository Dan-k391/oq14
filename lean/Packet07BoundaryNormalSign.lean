import Packet07BoundarySides

/-! A regular normal derivative has a fixed sign in a whole local ball. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryNormalSign
open Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem fixed_normal_sign (F : Space → ℝ) (x : Space) (i : Fin 3)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F x)
    (hi : fderiv ℝ F x (EuclideanSpace.single i 1) ≠ 0) :
    ∃ r > 0, (∀ y ∈ Metric.ball x r, 0 < fderiv ℝ F y (EuclideanSpace.single i 1)) ∨
      (∀ y ∈ Metric.ball x r, fderiv ℝ F y (EuclideanSpace.single i 1) < 0) := by
  let d : Space → ℝ := fun y => fderiv ℝ F y (EuclideanSpace.single i 1)
  have hd : ContinuousAt d x := by
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.continuousAt.comp
      ((hF.fderiv_right (m := 0) (by simp)).continuousAt)
  rcases lt_or_gt_of_ne hi with hn | hp
  · have he : ∀ᶠ y in 𝓝 x, d y < 0 := hd.eventually (Iio_mem_nhds hn)
    obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
    exact ⟨r,hr,Or.inr hball⟩
  · have he : ∀ᶠ y in 𝓝 x, 0 < d y := hd.eventually (Ioi_mem_nhds hp)
    obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
    exact ⟨r,hr,Or.inl hball⟩

end OQ14.Packet07BoundaryNormalSign
#print axioms OQ14.Packet07BoundaryNormalSign.fixed_normal_sign
