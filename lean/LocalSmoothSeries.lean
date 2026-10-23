import Mathlib.Analysis.Calculus.SmoothSeries

/-! Actual local termwise Frechet differentiation from summable derivative bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.LocalSmoothSeries
open Filter Set
open scoped Topology

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem local_derivative_summable (f : α → E → F) (N : ℕ) (s : Set E)
    (u : ℕ → α → ℝ) (hu : ∀ j, j ≤ N → Summable (u j))
    (hb : ∀ j, j ≤ N → ∀ a x,x∈s → ‖iteratedFDeriv ℝ j (f a) x‖ ≤ u j a)
    (j : ℕ) (hj : j ≤ N) (x : E) (hx : x∈s) :
    Summable (fun a => iteratedFDeriv ℝ j (f a) x) :=
  Summable.of_norm_bounded (u j) (hu j hj) (fun a => hb j hj a x hx)

theorem iteratedFDeriv_tsum_on_open (f : α → E → F) (hf : ∀ a,ContDiff ℝ (⊤ : ℕ∞) (f a))
    (N : ℕ) (s : Set E) (hs : IsOpen s) (hc : IsPreconnected s) (x₀ : E) (hx₀ : x₀∈s)
    (u : ℕ → α → ℝ) (hu : ∀ j, j ≤ N → Summable (u j))
    (hb : ∀ j, j ≤ N → ∀ a x,x∈s → ‖iteratedFDeriv ℝ j (f a) x‖ ≤ u j a) :
    ∀ j : ℕ,j ≤ N → ∀ x∈s,
      iteratedFDeriv ℝ j (fun y => ∑' a,f a y) x=∑' a,iteratedFDeriv ℝ j (f a) x := by
  intro j
  induction j with
  | zero =>
      intro _ x hx
      simp_rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum

  | succ j ih =>
      intro hj x hx
      have hjN : j ≤ N := (Nat.le_succ _).trans hj
      have he : (fun y => iteratedFDeriv ℝ j (fun z => ∑' a,f a z) y) =ᶠ[𝓝 x]
          fun y => ∑' a,iteratedFDeriv ℝ j (f a) y := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact ih hjN y hy
      have hnorm (a : α) (y : E) (hy : y∈s) :
          ‖fderiv ℝ (iteratedFDeriv ℝ j (f a)) y‖ ≤ u (j+1) a := by
        rw [fderiv_iteratedFDeriv,Function.comp_apply,LinearIsometryEquiv.norm_map]
        exact hb (j+1) hj a y hy
      have hd : HasFDerivAt (fun y => ∑' a,iteratedFDeriv ℝ j (f a) y)
          (∑' a,fderiv ℝ (iteratedFDeriv ℝ j (f a)) x) x :=
        hasFDerivAt_tsum_of_isPreconnected
        (f := fun a => iteratedFDeriv ℝ j (f a))
        (f' := fun a y => fderiv ℝ (iteratedFDeriv ℝ j (f a)) y)
        (hu (j+1) hj) hs hc
        (fun a y _ => ((hf a).differentiable_iteratedFDeriv
          (by exact_mod_cast ENat.coe_lt_top j) y).hasFDerivAt) hnorm hx₀
        (local_derivative_summable f N s u hu hb j hjN x₀ hx₀) hx
      simp_rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp_apply]
      rw [he.fderiv_eq,hd.fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

end OQ14.LocalSmoothSeries

#print axioms OQ14.LocalSmoothSeries.local_derivative_summable

#print axioms OQ14.LocalSmoothSeries.iteratedFDeriv_tsum_on_open
