import CompactPerturbation

/-! # The injective Fredholm alternative from compactness

The proof constructs separated images from strictly descending closed
power ranges. It does not assume an abstract Fredholm theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.CompactAlternative

open Metric Filter OQ14.CompactPerturbation
open scoped Topology InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem injective_antilipschitz (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (hinj : Function.Injective (defect T)) :
    ∃ C, AntilipschitzWith C (defect T) := by
  obtain ⟨C,hC,hb⟩ := norm_bound_on_subspace T hT ⊤ isClosed_univ (by
    intro x _ hx
    apply hinj
    simp only [defect_apply, hx, sub_self, map_zero])
  exact ⟨⟨C,hC.le⟩, (defect T).antilipschitz_of_bound (fun x => hb x (Submodule.mem_top))⟩

theorem power_antilipschitz (A : E →L[ℂ] E) {C : ℝ≥0}
    (hA : AntilipschitzWith C A) (n : ℕ) :
    AntilipschitzWith (C ^ n) (A ^ n) := by
  induction n with
  | zero => simpa using (AntilipschitzWith.id : AntilipschitzWith 1 (id : E → E))
  | succ n ih =>
    simpa only [pow_succ, ContinuousLinearMap.coe_mul, mul_comm C] using ih.comp hA

theorem power_range_closed [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (hinj : Function.Injective (defect T)) (n : ℕ) :
    IsClosed (LinearMap.range ((defect T) ^ n) : Set E) := by
  obtain ⟨C,hC⟩ := injective_antilipschitz T hT hinj
  exact (power_antilipschitz _ hC n).isClosed_range ((defect T)^n).uniformContinuous

theorem power_range_antitone (A : E →L[ℂ] E) :
    Antitone (fun n : ℕ => LinearMap.range (A ^ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rintro y ⟨x, hx⟩
  refine ⟨A x, ?_⟩
  simpa only [pow_succ, ContinuousLinearMap.mul_apply] using hx

theorem power_range_strict (A : E →L[ℂ] E) (hinj : Function.Injective A)
    (hns : ¬ Function.Surjective A) (n : ℕ) :
    LinearMap.range (A ^ (n+1)) < LinearMap.range (A ^ n) := by
  refine lt_of_le_of_ne (power_range_antitone A (Nat.le_succ n)) ?_
  intro he
  apply hns
  have hi (m : ℕ) : Function.Injective (A ^ m) := by
    induction m with
    | zero => simpa using Function.injective_id
    | succ m ih => simpa only [pow_succ, ContinuousLinearMap.mul_apply] using ih.comp hinj
  intro y
  have hy : (A^n) y ∈ LinearMap.range (A^(n+1)) := by
    rw [he]
    exact ⟨y,rfl⟩
  obtain ⟨x,hx⟩ := hy
  refine ⟨x, hi n ?_⟩
  simpa only [pow_succ, ContinuousLinearMap.mul_apply] using hx

theorem unit_orthogonal_of_lt [CompleteSpace E] (W V : Submodule ℂ E) (h : W < V)
    (hW : IsClosed (W : Set E)) :
    ∃ x : E, x ∈ V ∧ x ∈ Wᗮ ∧ ‖x‖ = 1 := by
  letI : CompleteSpace W := hW.completeSpace_coe
  obtain ⟨y,hyV,hyW⟩ := SetLike.exists_of_lt h
  let z : E := y - W.orthogonalProjection y
  have hzV : z ∈ V := V.sub_mem hyV (h.le (W.orthogonalProjection y).property)
  have hzW : z ∈ Wᗮ := W.sub_orthogonalProjection_mem_orthogonal y
  have hz : z ≠ 0 := by
    intro he
    have he' : y = (W.orthogonalProjection y : E) := sub_eq_zero.mp he
    exact hyW (he' ▸ (W.orthogonalProjection y).property)
  refine ⟨(‖z‖⁻¹ : ℂ) • z, V.smul_mem _ hzV, Wᗮ.smul_mem _ hzW, ?_⟩
  simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

/-- Injectivity of identity minus a compact operator implies surjectivity.
The proof uses actual separated images of a bounded sequence if the closed
power ranges were strictly descending. -/
theorem surjective_of_injective [CompleteSpace E] (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) (hinj : Function.Injective (defect T)) :
    Function.Surjective (defect T) := by
  by_contra hns
  let A := defect T
  let V : ℕ → Submodule ℂ E := fun n => LinearMap.range (A ^ n)
  have hv (n : ℕ) : ∃ x : E, x ∈ V n ∧ x ∈ (V (n+1))ᗮ ∧ ‖x‖ = 1 :=
    unit_orthogonal_of_lt (V (n+1)) (V n)
      (power_range_strict A hinj hns n) (power_range_closed T hT hinj (n+1))
  choose x hxV hxO hxn using hv
  have hax (n : ℕ) : A (x n) ∈ V (n+1) := by
    obtain ⟨y,hy⟩ := hxV n
    refine ⟨y, ?_⟩
    rw [pow_succ']
    change A ((A^n) y) = A (x n)
    rw [hy]
  have hTpres (n : ℕ) (y : E) (hy : y ∈ V n) : T y ∈ V n := by
    have ha : A y ∈ V (n+1) := by
      obtain ⟨z,hz⟩ := hy
      refine ⟨z, ?_⟩
      rw [pow_succ']
      change A ((A^n) z) = A y
      rw [hz]
    have hb := (V n).sub_mem hy (power_range_antitone A (Nat.le_succ n) ha)
    simpa only [A, defect_apply, sub_sub_cancel] using hb
  have hsep (n m : ℕ) (hnm : n < m) : 1 ≤ ‖T (x n) - T (x m)‖ := by
    have hm : T (x m) ∈ V (n+1) :=
      power_range_antitone A hnm (hTpres m (x m) (hxV m))
    have horth : ⟪A (x n) + T (x m), x n⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp (hxO n) _
        ((V (n+1)).add_mem (hax n) hm)
    have he : T (x n) - T (x m) = x n - (A (x n) + T (x m)) := by
      simp only [A, defect_apply]
      abel
    have hi : ⟪T (x n) - T (x m), x n⟫_ℂ = 1 := by
      rw [he, inner_sub_left, horth, sub_zero, inner_self_eq_norm_sq_to_K, hxn]
      norm_num
    have hb := norm_inner_le_norm (𝕜 := ℂ) (T (x n) - T (x m)) (x n)
    simpa only [hi, norm_one, hxn, mul_one] using hb
  have hc := hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨v, _, φ, hφ, hv⟩ := hc.tendsto_subseq (fun n =>
    subset_closure (Set.mem_image_of_mem T (show x n ∈ closedBall 0 1 by
      simp only [mem_closedBall, dist_zero_right, hxn, le_refl])))
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hv.cauchySeq 1 zero_lt_one
  have hd := hN (N+1) (Nat.le_succ N)
  have hs := hsep (φ N) (φ (N+1)) (hφ (Nat.lt_succ_self N))
  have hd' : ‖T (x (φ N)) - T (x (φ (N+1)))‖ < 1 := by
    simpa only [Function.comp_def, dist_eq_norm, norm_sub_rev] using hd
  exact (not_lt_of_ge hs) hd'

end OQ14.CompactAlternative

#print axioms OQ14.CompactAlternative.injective_antilipschitz
#print axioms OQ14.CompactAlternative.power_antilipschitz
#print axioms OQ14.CompactAlternative.power_range_closed
#print axioms OQ14.CompactAlternative.power_range_antitone
#print axioms OQ14.CompactAlternative.power_range_strict
#print axioms OQ14.CompactAlternative.unit_orthogonal_of_lt
#print axioms OQ14.CompactAlternative.surjective_of_injective
