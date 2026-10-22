import RadialFullMajorant
import RadialPhaseLimit

/-! Genuine all-degree scalar mixed-derivative series limits for actual finite stacks. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialScalarSeries

open Filter OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
open OQ14.RadialEntireReaction OQ14.RiccatiOriginSeries
open scoped Topology

theorem layers_bounds (gs : List Segment) (R : ℝ) (hR : 0 < R) (q M : ℝ)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ g ∈ layers gs R hR, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q := by
  induction gs generalizing R with
  | nil => simp only [layers,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons g gs ih =>
    intro a ha
    rw [layers,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih (R+g.width) (add_pos_of_pos_of_nonneg hR g.width_nonneg)
        (fun h hh => hp h (List.mem_cons_of_mem _ hh)) a ha
    · simpa only [Segment.layer] using hp g List.mem_cons_self

def actualTerm (gs : List Segment) (k m n : ℕ) (z w : ℂ) (j l : ℕ) : ℂ :=
  ((l+1 : ℝ)^k) • component l m n (layers gs (radius j) (radius_pos j))
    (radius j) (radius j+width gs) (radius_pos j) z w

def limitTerm (gs : List Segment) (k m n : ℕ) (z w : ℂ) (l : ℕ) : ℂ :=
  ((l+1 : ℝ)^k) • ((limitingCoefficients l gs).1/(limitingCoefficients l gs).2 *
    iteratedDeriv m (origin l) z*iteratedDeriv n (origin l) w)

theorem actualTerm_tendsto (gs : List Segment) (k m n : ℕ) (z w : ℂ) (l : ℕ) :
    Tendsto (fun j : ℕ => actualTerm gs k m n z w j l) atTop (𝓝 (limitTerm gs k m n z w l)) := by
  have h := ((actual_gamma_limit l gs).mul_const (iteratedDeriv m (origin l) z)).mul_const
    (iteratedDeriv n (origin l) w)
  exact h.const_smul ((l+1 : ℝ)^k)

theorem eventually_actual_majorant (gs : List Segment) (q M b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q)
    (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    ∀ᶠ j : ℕ in atTop, ∀ l : ℕ,
      ‖actualTerm gs k m n z w j l‖ ≤ RadialFullMajorant.majorant q M (width gs) b k l := by
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*b)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with j hR ht hd
  intro l
  have hparams := layers_bounds gs (radius j) (radius_pos j) q M hp
  have h := RadialFullMajorant.component_weighted_bound l k m n
    (layers_chain gs (radius j) (radius_pos j)) q M (width gs) b hq hM hR hb ht
    (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) z w hz hw
  simpa only [actualTerm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (l+1 : ℝ)^k)] using h

theorem eventually_actual_summable (gs : List Segment) (q M b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q)
    (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    ∀ᶠ j : ℕ in atTop, Summable (actualTerm gs k m n z w j) := by
  filter_upwards [eventually_actual_majorant gs q M b k m n hq hM hb hp z w hz hw] with j hj
  exact Summable.of_norm_bounded _ (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le) hj

theorem limiting_series_summable (gs : List Segment) (q M b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q)
    (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    Summable (limitTerm gs k m n z w) := by
  apply Summable.of_norm_bounded _ (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le)
  intro l
  apply le_of_tendsto (actualTerm_tendsto gs k m n z w l).norm
  filter_upwards [eventually_actual_majorant gs q M b k m n hq hM hb hp z w hz hw] with j hj
  exact hj l

theorem actual_series_limit (gs : List Segment) (q M b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q)
    (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    Tendsto (fun j : ℕ => ∑' l : ℕ, actualTerm gs k m n z w j l) atTop
      (𝓝 (∑' l : ℕ, limitTerm gs k m n z w l)) := by
  exact tendsto_tsum_of_dominated_convergence
    (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le)
    (actualTerm_tendsto gs k m n z w)
    (eventually_actual_majorant gs q M b k m n hq hM hb hp z w hz hw)

end OQ14.RadialScalarSeries

#print axioms OQ14.RadialScalarSeries.layers_bounds
#print axioms OQ14.RadialScalarSeries.actualTerm_tendsto
#print axioms OQ14.RadialScalarSeries.eventually_actual_majorant
#print axioms OQ14.RadialScalarSeries.eventually_actual_summable
#print axioms OQ14.RadialScalarSeries.limiting_series_summable
#print axioms OQ14.RadialScalarSeries.actual_series_limit
