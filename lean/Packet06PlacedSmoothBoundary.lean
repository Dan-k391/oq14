import Packet06PlacementHomeomorph
import Packet05RoundedModeMaterial

/-! Smooth regular material interfaces survive the actual rotated Maxwell
placement, including the nonvanishing differential of a defining function. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedSmoothBoundary
open Set Metric Maxwell Packet06PlacementHomeomorph Packet06CyclicRotation

theorem smooth_boundary_image (s : ℝ) (hs : 0 < s) (a : Space) (S : Set Space)
    (hS : ∀ y ∈ frontier S, ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F y ∧ F y=0 ∧
      fderiv ℝ F y ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ y ∈ U ∧
        ∀ z ∈ U, (z ∈ S ↔ 0 < F z)) :
    ∀ x ∈ frontier (placement s hs a '' S), ∃ F : Space → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ z ∈ U, (z ∈ placement s hs a '' S ↔ 0 < F z) := by
  let h := placement s hs a
  intro x hx
  have hx' : h.symm x ∈ frontier S := by
    rw [← h.image_frontier, h.image_eq_preimage] at hx
    exact hx
  obtain ⟨F,hF,hzero,hder,U,hU,hxU,hlevel⟩ := hS _ hx'
  let L : Space →L[ℝ] Space := rotation.symm.toContinuousLinearMap.comp
    (s • ContinuousLinearMap.id ℝ Space)
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => h.symm y) x := by
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun y => rotation.symm (s • (y-a))) x
    exact (rotation.symm.toContinuousLinearMap.contDiff.comp
      (contDiff_const.smul (contDiff_id.sub contDiff_const))).contDiffAt
  have hmapD : HasFDerivAt (fun y => h.symm y) L x := by
    exact rotation.symm.toContinuousLinearMap.hasFDerivAt.comp x
      (((ContinuousLinearMap.id ℝ Space).hasFDerivAt.sub_const a).const_smul s)
  let G : Space → ℝ := fun y => F (h.symm y)
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G x := hF.comp x hmap
  have hGD : HasFDerivAt G ((fderiv ℝ F (h.symm x)).comp L) x :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp x hmapD
  have hne : fderiv ℝ G x ≠ 0 := by
    intro hz
    have hz' : (fderiv ℝ F (h.symm x)).comp L=0 := by rw [← hGD.fderiv,hz]
    apply hder
    ext v
    have hv := congrArg (fun T : Space →L[ℝ] ℝ => T (s⁻¹ • rotate v)) hz'
    change (fderiv ℝ F (h.symm x)) (unrotate (s • (s⁻¹ • rotate v)))=0 at hv
    simpa only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul,unrotate_rotate] using hv
  refine ⟨G,hG,hzero,hne,h.symm ⁻¹' U,hU.preimage h.symm.continuous,hxU,?_⟩
  intro y hy
  rw [h.image_eq_preimage]
  exact hlevel _ hy

end OQ14.Packet06PlacedSmoothBoundary
#print axioms OQ14.Packet06PlacedSmoothBoundary.smooth_boundary_image
