import HilbertFiniteRank

/-! A uniformly bounded strongly convergent operator sequence converges
in operator norm after composition on the right with a fixed compact map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06StrongCompact
open Metric Filter Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem compact_right_norm_tendsto (T : ℕ → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖T n‖ ≤ C) (hstrong : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 0))
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    Tendsto (fun n => (T n).comp K) atTop (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε/(4*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : C*δ ≤ ε/4 := by
    dsimp [δ]
    have hc : 0 < 4*(C+1) := by positivity
    have haux : C * ε ≤ (C+1)*ε := by nlinarith
    have heq : C * (ε / (4*(C+1))) = (C*ε)/(4*(C+1)) := by ring
    rw [heq, div_le_iff₀ hc]
    nlinarith
  have hc := hK.isCompact_closure_image_closedBall (f := K.toLinearMap) 1
  obtain ⟨s,_,hs,hcover⟩ := hc.finite_cover_balls hδ
  have hfin : ∀ᶠ n in atTop, ∀ v ∈ hs.toFinset, ‖T n v‖ < ε/4 := by
    apply (Finset.eventually_all hs.toFinset).mpr
    intro v hv
    have he := (hstrong v).eventually (Metric.ball_mem_nhds (0 : F) (show 0 < ε/4 by positivity))
    filter_upwards [he] with n hn
    simpa only [mem_ball, dist_zero_right] using hn
  have hunit : ∀ᶠ n in atTop, ∀ x : E, ‖x‖ = 1 → ‖T n (K x)‖ ≤ ε/2 := by
    filter_upwards [hfin] with n hn x hx
    have hxin : K x ∈ closure (K.toLinearMap '' closedBall (0 : E) 1) :=
      subset_closure (Set.mem_image_of_mem K.toLinearMap (by simp [mem_closedBall,hx]))
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp (hcover hxin)
    obtain ⟨hvs,hball⟩ := Set.mem_iUnion.mp hv
    have hv' : v ∈ hs.toFinset := hs.mem_toFinset.mpr hvs
    have hd : ‖K x-v‖ < δ := by simpa only [mem_ball,dist_eq_norm] using hball
    have ht : ‖T n (K x-v)‖ ≤ C*‖K x-v‖ :=
      ((T n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
    have hsum : ‖T n (K x)‖ ≤ ‖T n (K x-v)‖ + ‖T n v‖ := by
      have he : T n (K x) = T n (K x-v) + T n v := by rw [map_sub]; abel
      rw [he]
      exact norm_add_le _ _
    have hscale : C*‖K x-v‖ ≤ C*δ := mul_le_mul_of_nonneg_left hd.le hC
    linarith [hn v hv',hscale,hδbound]
  have hnorm : ∀ᶠ n in atTop, ‖(T n).comp K‖ ≤ ε/2 := by
    filter_upwards [hunit] with n hn
    refine ContinuousLinearMap.opNorm_le_bound' _ (half_pos hε).le ?_
    intro x hx
    let y : E := (‖x‖⁻¹ : ℂ) • x
    have hy : ‖y‖ = 1 := by
      simp only [y,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm]
      exact inv_mul_cancel₀ hx
    have hh := hn y hy
    change ‖((T n).comp K) ((‖x‖⁻¹ : ℂ) • x)‖ ≤ ε/2 at hh
    rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm,
      ← div_eq_inv_mul, div_le_iff₀ ((norm_nonneg x).lt_of_ne' hx)] at hh
    exact hh
  have he : ∀ᶠ n in atTop, dist (‖(T n).comp K‖) 0 < ε := by
    filter_upwards [hnorm] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using lt_of_le_of_lt hn (half_lt_self hε)
  exact eventually_atTop.mp he

/-- The same norm convergence is uniform over any norm-compact continuous
family of compact operators, such as a compact set of frequencies. -/
theorem compact_family_uniform {X : Type*} [TopologicalSpace X]
    (T : ℕ → E →L[ℂ] F) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖T n‖ ≤ C) (hstrong : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 0))
    (K : X → E →L[ℂ] E) (D : Set X) (hD : IsCompact D)
    (hcont : ContinuousOn K D) (hK : ∀ z ∈ D, IsCompactOperator (K z)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ D, ‖(T n).comp (K z)‖ < ε := by
  classical
  intro ε hε
  let δ : ℝ := ε/(4*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : C*δ ≤ ε/4 := by
    dsimp [δ]
    have hc : 0 < 4*(C+1) := by positivity
    have haux : C*ε ≤ (C+1)*ε := by nlinarith
    have heq : C*(ε/(4*(C+1))) = (C*ε)/(4*(C+1)) := by ring
    rw [heq,div_le_iff₀ hc]
    nlinarith
  have hc := hD.image_of_continuousOn hcont
  obtain ⟨s,hsD,hs,hcover⟩ := hc.finite_cover_balls hδ
  have hfin : ∀ᶠ n in atTop, ∀ A ∈ hs.toFinset, ‖(T n).comp A‖ < ε/4 := by
    apply (Finset.eventually_all hs.toFinset).mpr
    intro A hAs
    have hA : A ∈ K '' D := hsD (hs.mem_toFinset.mp hAs)
    obtain ⟨z,hz,rfl⟩ := hA
    have ht := compact_right_norm_tendsto T C hC hb hstrong (K z) (hK z hz)
    have he := ht.eventually (Metric.ball_mem_nhds 0 (show 0 < ε/4 by positivity))
    filter_upwards [he] with n hn
    simpa only [mem_ball,dist_zero_right] using hn
  filter_upwards [hfin] with n hn z hz
  obtain ⟨A,hA⟩ := Set.mem_iUnion.mp (hcover (Set.mem_image_of_mem K hz))
  obtain ⟨hAs,hball⟩ := Set.mem_iUnion.mp hA
  have hclose : ‖K z-A‖ < δ := by simpa only [mem_ball,dist_eq_norm] using hball
  have hsmall := hn A (hs.mem_toFinset.mpr hAs)
  have he : (T n).comp (K z) = (T n).comp (K z-A) + (T n).comp A := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, map_sub]
    abel
  rw [he]
  have hnrm : ‖(T n).comp (K z-A)‖ ≤ C*‖K z-A‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
  have hscale : C*‖K z-A‖ ≤ C*δ := mul_le_mul_of_nonneg_left hclose.le hC
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith [hnrm,hscale,hδbound,hsmall])

#print axioms OQ14.Packet06StrongCompact.compact_right_norm_tendsto
#print axioms OQ14.Packet06StrongCompact.compact_family_uniform
end OQ14.Packet06StrongCompact
