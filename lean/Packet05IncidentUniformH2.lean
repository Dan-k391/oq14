import Packet05SmoothIncidentH2
import Packet05LocalizedAnisotropic

/-! A fixed smooth compact incident field preserves family-uniform H² bounds. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05IncidentUniformH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05SmoothIncidentH2 OQ14.Packet05LocalizedAnisotropic

theorem fixed_smooth_addition {A : Type*} (u : A → L2Scalar) (N : ℝ) (hN : 0 ≤ N)
    (hu : ∀ a, ∃ D : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ i, HasWeakPartial (u a) (D i) i) ∧
      (∀ i j, HasWeakPartial (D i) (H i j) j) ∧
      ‖u a‖ ≤ N ∧ (∀ i, ‖D i‖ ≤ N) ∧ (∀ i j, ‖H i j‖ ≤ N))
    (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a, ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ H : Fin 3 → Fin 3 → L2Scalar,
      (∀ i, HasWeakPartial U (D i) i) ∧ (∀ i j, HasWeakPartial (D i) (H i j) j) ∧
      (∀ᵐ x ∂volume, U x = u a x + f x) ∧
      ‖U‖ ≤ K ∧ (∀ i, ‖D i‖ ≤ K) ∧ (∀ i j, ‖H i j‖ ≤ K) := by
  obtain ⟨v,hv,hval⟩ := compact_smooth_h2 f hf hc
  obtain ⟨G,H,hG,hH⟩ := hv
  let B := ‖v‖ + (∑ i : Fin 3, ‖G i‖) + ∑ i : Fin 3, ∑ j : Fin 3, ‖H i j‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hvB : ‖v‖ ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ ∑ i : Fin 3, ‖G i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H i j‖ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    linarith
  have hGB (i : Fin 3) : ‖G i‖ ≤ B := by
    have h1 := Finset.single_le_sum (f := fun i : Fin 3 => ‖G i‖) (fun i _ => norm_nonneg (G i)) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H i j‖ := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    dsimp [B]
    linarith [norm_nonneg v]
  have hHB (i j : Fin 3) : ‖H i j‖ ≤ B := by
    have h1 := Finset.single_le_sum (f := fun j : Fin 3 => ‖H i j‖) (fun j _ => norm_nonneg (H i j)) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3, ‖H i j‖)
      (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (H i j))) (Finset.mem_univ i)
    have h3 : 0 ≤ ∑ i : Fin 3, ‖G i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [B]
    linarith [norm_nonneg v]
  refine ⟨N+B,add_nonneg hN hB,?_⟩
  intro a
  obtain ⟨D,T,hD,hT,hun,hDn,hTn⟩ := hu a
  refine ⟨u a+v,fun i => D i+G i,fun i j => T i j+H i j,
    (fun i => weak_partial_add _ _ _ _ i (hD i) (hG i)),
    (fun i j => weak_partial_add _ _ _ _ j (hT i j) (hH i j)),?_,?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_add (u a) v,hval] with x hx hy
    rw [hx]
    simp only [Pi.add_apply,hy]
  · exact (norm_add_le _ _).trans (add_le_add hun hvB)
  · intro i
    exact (norm_add_le _ _).trans (add_le_add (hDn i) (hGB i))
  · intro i j
    exact (norm_add_le _ _).trans (add_le_add (hTn i j) (hHB i j))

end OQ14.Packet05IncidentUniformH2
#print axioms OQ14.Packet05IncidentUniformH2.fixed_smooth_addition
