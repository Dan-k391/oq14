import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Genuine preservation of essential-volume peaks under strong L2 convergence. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.L2PeakPreservation
open MeasureTheory Set Filter
open scoped Topology
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

def boundedOn (S : Set α) (M : ℝ) : Set (Lp E 2 μ) :=
  {f | ∀ᵐ x : α ∂μ.restrict S, ‖f x‖ ≤ M}

theorem isClosed_boundedOn (S : Set α) (M : ℝ) : IsClosed (boundedOn (μ := μ) (E := E) S M) := by
  apply IsSeqClosed.isClosed
  intro f f₀ hf ht
  obtain ⟨φ,_,hφ⟩ := tendstoInMeasure_of_tendsto_Lp ht |>.exists_seq_tendsto_ae
  have hb : ∀ᵐ x : α ∂μ.restrict S, ∀ n : ℕ, ‖f (φ n) x‖ ≤ M :=
    ae_all_iff.mpr (fun n => hf (φ n))
  filter_upwards [hb,ae_restrict_of_ae hφ] with x hx htx
  exact le_of_tendsto' htx.norm (fun n => hx n)

theorem eventually_exceeds (S : Set α) (f : ℕ → Lp E 2 μ) (f₀ : Lp E 2 μ)
    (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ¬∃ M : ℝ, ∀ᵐ x : α ∂μ.restrict S, ‖f₀ x‖ ≤ M) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ¬∀ᵐ x : α ∂μ.restrict S, ‖f n x‖ ≤ M := by
  have hn : f₀ ∉ boundedOn S M := fun h => hu ⟨M,h⟩
  exact hf.eventually ((isClosed_boundedOn S M).isOpen_compl.mem_nhds hn)

theorem eventually_positive_superlevel (S : Set α) (f : ℕ → Lp E 2 μ) (f₀ : Lp E 2 μ)
    (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ¬∃ M : ℝ, ∀ᵐ x : α ∂μ.restrict S, ‖f₀ x‖ ≤ M) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < (μ.restrict S) {x | M < ‖f n x‖} := by
  filter_upwards [eventually_exceeds S f f₀ hf hu M] with n hn
  rw [ae_iff] at hn
  exact pos_iff_ne_zero.mpr (by simpa only [not_le] using hn)

end OQ14.L2PeakPreservation

#print axioms OQ14.L2PeakPreservation.isClosed_boundedOn
#print axioms OQ14.L2PeakPreservation.eventually_exceeds
#print axioms OQ14.L2PeakPreservation.eventually_positive_superlevel
