import Packet07AngularTranslation

/-! Smooth regular-level boundary certificates are preserved by affine scaling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07AffineSmooth
open Set Metric Packet07AffineGeometry
abbrev Space := Maxwell.Space

def homeo (s : ℝ) (hs : s ≠ 0) (a : Space) : Space ≃ₜ Space :=
  (Homeomorph.addRight (-a)).trans (Homeomorph.smulOfNeZero s hs)

theorem homeo_apply (s : ℝ) (hs : s ≠ 0) (a x : Space) : homeo s hs a x = map s a x := by
  simp [homeo, map, sub_eq_add_neg]

/-- Pulling back a regular local defining function by an invertible affine map
    preserves the full smooth boundary certificate. -/
theorem smooth_boundary_preimage (s : ℝ) (hs : s ≠ 0) (a : Space) (S : Set Space)
    (hS : ∀ y ∈ frontier S, ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F y ∧ F y = 0 ∧
      fderiv ℝ F y ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, (z ∈ S ↔ 0 < F z)) :
    ∀ x ∈ frontier (map s a ⁻¹' S), ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, (z ∈ map s a ⁻¹' S ↔ 0 < F z) := by
  intro x hx
  have he : (homeo s hs a : Space → Space) = map s a := funext (homeo_apply s hs a)
  have hx' : map s a x ∈ frontier S := by
    have hh := (homeo s hs a).preimage_frontier S
    rw [he] at hh
    exact (Set.mem_preimage.mp (hh ▸ hx))
  obtain ⟨F,hF,hzero,hder,U,hU,hxU,hlevel⟩ := hS _ hx'
  let G : Space → ℝ := F ∘ map s a
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞) (map s a) x := by
    exact (contDiff_const.smul (contDiff_id.sub contDiff_const)).contDiffAt
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G x := hF.comp x hmap
  have hmapD : HasFDerivAt (map s a) (s • ContinuousLinearMap.id ℝ Space) x := by
    simpa only [map] using (((ContinuousLinearMap.id ℝ Space).hasFDerivAt.sub_const a).const_smul s)
  have hGD : HasFDerivAt G ((fderiv ℝ F (map s a x)).comp (s • ContinuousLinearMap.id ℝ Space)) x :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp x hmapD
  have hne : fderiv ℝ G x ≠ 0 := by
    intro hz
    have hz' : (fderiv ℝ F (map s a x)).comp (s • ContinuousLinearMap.id ℝ Space) = 0 := by
      rw [← hGD.fderiv, hz]
    apply hder
    ext v
    have hv := congrArg (fun L : Space →L[ℝ] ℝ => L (s⁻¹ • v)) hz'
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hs, one_smul,
      ContinuousLinearMap.zero_apply] using hv
  refine ⟨G,hG,hzero,hne,map s a ⁻¹' U,hU.preimage (map_continuous s a),hxU,?_⟩
  intro z hz
  exact hlevel _ hz

end OQ14.Packet07AffineSmooth
#print axioms OQ14.Packet07AffineSmooth.homeo_apply
#print axioms OQ14.Packet07AffineSmooth.smooth_boundary_preimage
