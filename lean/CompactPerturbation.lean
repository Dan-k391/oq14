import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Genuine kernel and range consequences of compact perturbations

The compactness hypothesis below is the usual compact-operator definition.
No Fredholm alternative or closed-range conclusion is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.CompactPerturbation

open Metric Filter
open scoped Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def defect (T : E →L[ℂ] E) : E →L[ℂ] E := 1 - T

theorem defect_apply (T : E →L[ℂ] E) (x : E) : defect T x = x - T x := rfl

theorem kernel_finiteDimensional (T : E →L[ℂ] E) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker (defect T)) := by
  let V := LinearMap.ker (defect T)
  have hv (v : E) (h : v ∈ V) : T v = v := by
    exact (sub_eq_zero.mp h).symm
  have hi : ∀ v ∈ V, T.toLinearMap v ∈ V := by
    intro v h
    change T v ∈ V
    rw [hv v h]
    exact h
  have hr := hT.restrict hi (ContinuousLinearMap.isClosed_ker (defect T))
  have he : T.toLinearMap.restrict hi = LinearMap.id (R := ℂ) (M := V) := by
    ext v
    exact hv v.val v.property
  rw [he] at hr
  have hb := hr.isCompact_closure_image_closedBall (f := LinearMap.id (R := ℂ) (M := V)) 1
  have hb' : IsCompact (closedBall (0 : V) 1) := by
    simpa using hb
  exact FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hb'

/-- On a closed subspace with no nonzero fixed point, the defect has a
positive lower bound on the unit sphere. -/
theorem sphere_gap (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hfix : ∀ x ∈ V, T x = x → x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ V, ‖x‖ = 1 → ε ≤ ‖defect T x‖ := by
  by_contra h
  push_neg at h
  have hn (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity
  choose u huV hun huA using fun n : ℕ => h (1 / (n + 1)) (hn n)
  have hc := hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨v, _, φ, hφ, hv⟩ := hc.tendsto_subseq (fun n =>
    subset_closure (Set.mem_image_of_mem T (show u n ∈ closedBall 0 1 by
      simp only [mem_closedBall, dist_zero_right, hun n, le_refl])))
  have hzero : Tendsto (fun n => defect T (u n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => (huA n).le)
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hx : Tendsto (u ∘ φ) atTop (𝓝 v) := by
    have ha := (hzero.comp hφ.tendsto_atTop).add hv
    simpa only [Function.comp_def, defect_apply, sub_add_cancel, zero_add] using ha
  have hvV : v ∈ V := hV.mem_of_tendsto hx (Eventually.of_forall fun n => huV (φ n))
  have hvn : ‖v‖ = 1 := tendsto_nhds_unique (hx.norm) (by
    simpa only [Function.comp_def, hun] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hva : defect T v = 0 := tendsto_nhds_unique
    ((defect T).continuous.tendsto v |>.comp hx) (hzero.comp hφ.tendsto_atTop)
  have hv0 := hfix v hvV ((sub_eq_zero.mp hva).symm)
  simp [hv0] at hvn

theorem norm_bound_on_subspace (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hfix : ∀ x ∈ V, T x = x → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V, ‖x‖ ≤ C * ‖defect T x‖ := by
  obtain ⟨ε, hε, hg⟩ := sphere_gap T hT V hV hfix
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro x hx
  by_cases hz : x = 0
  · simp [hz]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
  let u : E := (‖x‖⁻¹ : ℂ) • x
  have hnu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hgu := hg u (V.smul_mem _ hx) hnu
  have he : ‖defect T u‖ = ‖x‖⁻¹ * ‖defect T x‖ := by
    simp only [u, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm]
  rw [he] at hgu
  have hle : ε * ‖x‖ ≤ ‖defect T x‖ := by
    have hh := mul_le_mul_of_nonneg_right hgu hn.le
    calc
      ε * ‖x‖ ≤ (‖x‖⁻¹ * ‖defect T x‖) * ‖x‖ := hh
      _ = ‖defect T x‖ := by field_simp
  exact (le_inv_mul_iff₀ hε).mpr hle

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem orthogonal_norm_bound (T : E →L[ℂ] E) (hT : IsCompactOperator T) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ (LinearMap.ker (defect T))ᗮ,
      ‖x‖ ≤ C * ‖defect T x‖ := by
  apply norm_bound_on_subspace T hT _ (Submodule.isClosed_orthogonal _)
  intro x hx htx
  have hk : x ∈ LinearMap.ker (defect T) := by
    change x - T x = 0
    rw [htx, sub_self]
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hx x hk)

theorem range_closed [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsCompactOperator T) :
    IsClosed (Set.range (defect T)) := by
  let K := LinearMap.ker (defect T)
  let V := Kᗮ
  let A : V →L[ℂ] E := (defect T).comp V.subtypeL
  have hK : IsClosed (K : Set E) := ContinuousLinearMap.isClosed_ker (defect T)
  letI : CompleteSpace K := hK.completeSpace_coe
  letI : CompleteSpace V := (Submodule.isClosed_orthogonal K).completeSpace_coe
  obtain ⟨C, hC, hb⟩ := orthogonal_norm_bound T hT
  have hanti : AntilipschitzWith ⟨C, hC.le⟩ A :=
    A.antilipschitz_of_bound (fun x => hb x.val x.property)
  have hr : IsClosed (Set.range A) := hanti.isClosed_range A.uniformContinuous
  have he : Set.range A = Set.range (defect T) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x - K.orthogonalProjection x,
        K.sub_orthogonalProjection_mem_orthogonal x⟩, ?_⟩
      change defect T (x - (K.orthogonalProjection x : E)) = defect T x
      rw [map_sub]
      have hk : defect T (K.orthogonalProjection x : E) = 0 :=
        (K.orthogonalProjection x).property
      rw [hk, sub_zero]
  rwa [he] at hr

end OQ14.CompactPerturbation

#print axioms OQ14.CompactPerturbation.defect_apply
#print axioms OQ14.CompactPerturbation.kernel_finiteDimensional
#print axioms OQ14.CompactPerturbation.sphere_gap
#print axioms OQ14.CompactPerturbation.norm_bound_on_subspace
#print axioms OQ14.CompactPerturbation.orthogonal_norm_bound
#print axioms OQ14.CompactPerturbation.range_closed
