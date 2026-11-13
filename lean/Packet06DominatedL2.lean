import Packet06WeightedAngularLimit
import L2Parametric
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06DominatedL2
open MeasureTheory Filter OQ14.Maxwell
open scoped Topology

theorem toLp_tendsto (f : ℕ → Space → ℂ) (g : Space → ℂ)
    (hf : ∀ j, MemLp (f j) 2 volume) (hg : MemLp g 2 volume)
    (H : Space → ℝ) (hH : Integrable H)
    (hbound : ∀ j, ∀ᵐ x : Space, ‖f j x-g x‖^2 ≤ H x)
    (hpoint : ∀ᵐ x : Space, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun x : Space => ‖f j x-g x‖^2) volume :=
    (((hf j).aestronglyMeasurable).sub hg.aestronglyMeasurable).norm.pow 2
  have hdom := tendsto_integral_filter_of_dominated_convergence H (Eventually.of_forall hmeas)
    (Eventually.of_forall (fun j => (hbound j).mono (fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f j x-g x‖)]
      exact hx))) hH
    (hpoint.mono (fun x hx => by simpa using (hx.sub_const (g x)).norm.pow 2))
  have hsquare : Tendsto (fun j => ‖(hf j).toLp (f j)-hg.toLp g‖^2) atTop (𝓝 0) := by
    have he (j : ℕ) : ‖(hf j).toLp (f j)-hg.toLp g‖^2 = ∫ x : Space, ‖f j x-g x‖^2 := by
      rw [L2Parametric.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hf j).toLp (f j)) (hg.toLp g), (hf j).coeFn_toLp, hg.coeFn_toLp] with x hs hf' hg'
      simp only [hs,Pi.sub_apply,hf',hg']
    simpa only [he,integral_zero] using hdom
  have hn : Tendsto (fun j => ‖(hf j).toLp (f j)-hg.toLp g‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using h
  exact (tendsto_iff_norm_sub_tendsto_zero).2 hn
#print axioms OQ14.Packet06DominatedL2.toLp_tendsto
end OQ14.Packet06DominatedL2
