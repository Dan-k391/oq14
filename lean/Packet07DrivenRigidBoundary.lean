import Packet07DrivenRigidGeometry
import Packet05RoundedModeMaterial

/-! Rigid frame placement preserves the regularity of every material boundary. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet07DrivenRigidBoundary
open Set Packet07DrivenRigidHotspot Packet07PlaneFrame

theorem smooth_boundary (θ φ : ℝ) (a : Maxwell.Space) (S : Set Maxwell.Space)
    (hS : ∀ y ∈ frontier S, ∃ F : Maxwell.Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F y ∧ F y=0 ∧
      fderiv ℝ F y ≠ 0 ∧ ∃ U : Set Maxwell.Space, IsOpen U ∧ y ∈ U ∧
        ∀ z ∈ U, (z ∈ S ↔ 0 < F z)) :
    ∀ x ∈ frontier (placement θ φ a '' S), ∃ F : Maxwell.Space → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧
        ∀ z ∈ U, (z ∈ placement θ φ a '' S ↔ 0 < F z) := by
  let h := placement θ φ a
  intro x hx
  have hx' : h.symm x ∈ frontier S := by
    rw [← h.image_frontier, h.image_eq_preimage] at hx
    exact hx
  obtain ⟨F,hF,hzero,hder,U,hU,hxU,hlevel⟩ := hS _ hx'
  let L := (normalRotation θ φ).symm.toContinuousLinearMap
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => h.symm y) x := by
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (normalRotation θ φ).symm (y-a)) x
    exact ((normalRotation θ φ).symm.toContinuousLinearMap.contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have hmapD : HasFDerivAt (fun y => h.symm y) L x := by
    exact (normalRotation θ φ).symm.toContinuousLinearMap.hasFDerivAt.comp x
      ((ContinuousLinearMap.id ℝ Maxwell.Space).hasFDerivAt.sub_const a)
  let G : Maxwell.Space → ℝ := fun y => F (h.symm y)
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G x := hF.comp x hmap
  have hGD : HasFDerivAt G ((fderiv ℝ F (h.symm x)).comp L) x :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp x hmapD
  have hne : fderiv ℝ G x ≠ 0 := by
    intro hz
    have hz' : (fderiv ℝ F (h.symm x)).comp L=0 := by rw [← hGD.fderiv,hz]
    apply hder
    ext v
    have hv := congrArg (fun T : Maxwell.Space →L[ℝ] ℝ => T (normalRotation θ φ v)) hz'
    change (fderiv ℝ F (h.symm x)) ((normalRotation θ φ).symm (normalRotation θ φ v)) = 0 at hv
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hv
  refine ⟨G,hG,hzero,hne,h.symm ⁻¹' U,hU.preimage h.symm.continuous,hxU,?_⟩
  intro y hy
  rw [h.image_eq_preimage]
  exact hlevel _ hy
end OQ14.Packet07DrivenRigidBoundary
#print axioms OQ14.Packet07DrivenRigidBoundary.smooth_boundary
