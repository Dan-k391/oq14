import CompactPerturbation

/-! # Actual finite-rank approximation of compact Hilbert operators

A finite net of the compact image of the unit ball spans a finite-dimensional
space. Orthogonal projection onto this span approximates the operator in norm.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.HilbertFiniteRank

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem projection_residual_le (V : Submodule ℂ E) [FiniteDimensional ℂ V]
    (x : E) (v : V) : ‖x - (V.orthogonalProjection x : E)‖ ≤ ‖x - (v : E)‖ := by
  rw [Submodule.orthogonalProjection_minimal]
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro y ⟨w, rfl⟩
  exact norm_nonneg _

theorem factor_approx (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Submodule ℂ E), ∃ _ : FiniteDimensional ℂ V,
      ∃ B : E →L[ℂ] V, ‖T - V.subtypeL.comp B‖ < ε := by
  have hc := hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨s, _, hs, hcover⟩ := hc.finite_cover_balls (half_pos hε)
  let V : Submodule ℂ E := Submodule.span ℂ s
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ hs
  let B : E →L[ℂ] V := V.orthogonalProjection.comp T
  let F : E →L[ℂ] E := V.subtypeL.comp B
  have hunit (u : E) (hu : ‖u‖ = 1) : ‖(T-F) u‖ ≤ ε/2 := by
    have hin : T u ∈ closure (T.toLinearMap '' closedBall 0 1) :=
      subset_closure (Set.mem_image_of_mem T.toLinearMap (by simp [mem_closedBall, hu]))
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover hin)
    obtain ⟨hvs, hball⟩ := Set.mem_iUnion.mp hv
    have hdist : ‖T u - v‖ < ε/2 := by simpa only [mem_ball, dist_eq_norm] using hball
    have hp := projection_residual_le V (T u) ⟨v, Submodule.subset_span hvs⟩
    exact hp.trans hdist.le
  have hnorm : ‖T-F‖ ≤ ε/2 := by
    refine ContinuousLinearMap.opNorm_le_bound' _ (half_pos hε).le ?_
    intro x hx
    let u : E := (‖x‖⁻¹ : ℂ) • x
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ hx
    have hh := hunit u hu
    change ‖(T-F) ((‖x‖⁻¹ : ℂ) • x)‖ ≤ ε/2 at hh
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      ← div_eq_inv_mul, div_le_iff₀ ((norm_nonneg x).lt_of_ne' hx)] at hh
    exact hh
  exact ⟨V, inferInstance, B, hnorm.trans_lt (half_lt_self hε)⟩

theorem finite_rank_approx (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : E →L[ℂ] E, FiniteDimensional ℂ (LinearMap.range F) ∧ ‖T-F‖ < ε := by
  obtain ⟨V, hV, B, hB⟩ := factor_approx T hT ε hε
  letI : FiniteDimensional ℂ V := hV
  refine ⟨V.subtypeL.comp B, ?_, hB⟩
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rintro y ⟨x, rfl⟩
  exact (B x).property

end OQ14.HilbertFiniteRank

#print axioms OQ14.HilbertFiniteRank.projection_residual_le
#print axioms OQ14.HilbertFiniteRank.factor_approx
#print axioms OQ14.HilbertFiniteRank.finite_rank_approx
