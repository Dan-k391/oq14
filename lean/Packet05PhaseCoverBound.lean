import Packet05PhaseGluing

/-! Finite local charts preserve quantitative phase bounds when their actual
field representatives are glued. The selected cover is independent of the field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05PhaseCoverBound
open MeasureTheory Set Maxwell Packet05PhaseGluing

theorem finite_uniform_gluing {J A : Type*} [Fintype J]
    (U : Set Space) (hU : IsOpen U) (O : J → Set Space) (hO : ∀ j, IsOpen (O j))
    (E : A → Space → ℂ) (f : A → J → Space → ℂ)
    (hf : ∀ a j, Continuous (f a j))
    (hae : ∀ a j, f a j =ᵐ[volume.restrict (U ∩ O j)] E a)
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (data : A → ℝ) (hdata : ∀ a, 0 ≤ data a)
    (hbound : ∀ a j x, x ∈ closure U ∩ O j → ‖f a j x‖ ≤ B j*data a) :
    ∃ F : A → Space → ℂ,
      (∀ a, ContinuousOn (F a) (closure U ∩ ⋃ j, O j)) ∧
      (∀ a j, EqOn (F a) (f a j) (closure U ∩ O j)) ∧
      (∀ a, F a =ᵐ[volume.restrict (U ∩ ⋃ j, O j)] E a) ∧
      ∀ a x, x ∈ closure U ∩ ⋃ j, O j → ‖F a x‖ ≤ (∑ j, B j)*data a := by
  classical
  choose F hc he hae' using fun a => finite_phase_gluing U hU O hO (E a) (f a) (hf a) (hae a)
  refine ⟨F,hc,he,hae',?_⟩
  intro a x hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp hx.2
  rw [he a j ⟨hx.1,hj⟩]
  apply (hbound a j x ⟨hx.1,hj⟩).trans
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)) (hdata a)

theorem compact_uniform_gluing {J A : Type*}
    (K U : Set Space) (hK : IsCompact K) (hU : IsOpen U)
    (O : J → Set Space) (hO : ∀ j, IsOpen (O j)) (hcover : K ⊆ ⋃ j, O j)
    (E : A → Space → ℂ) (f : A → J → Space → ℂ)
    (hf : ∀ a j, Continuous (f a j))
    (hae : ∀ a j, f a j =ᵐ[volume.restrict (U ∩ O j)] E a)
    (B : J → ℝ) (hB : ∀ j, 0 ≤ B j) (data : A → ℝ) (hdata : ∀ a, 0 ≤ data a)
    (hbound : ∀ a j x, x ∈ closure U ∩ O j → ‖f a j x‖ ≤ B j*data a) :
    ∃ (V : Set Space) (C : ℝ) (F : A → Space → ℂ),
      IsOpen V ∧ K ⊆ V ∧ 0 ≤ C ∧
      (∃ t : Finset J, C=∑ j ∈ t, B j) ∧
      (∀ a, ContinuousOn (F a) (closure U ∩ V)) ∧
      (∀ a, F a =ᵐ[volume.restrict (U ∩ V)] E a) ∧
      ∀ a x, x ∈ closure U ∩ V → ‖F a x‖ ≤ C*data a := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover O hO hcover
  let V : Set Space := ⋃ j : t, O j
  have hc : K ⊆ V := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩
  obtain ⟨F,hFc,hFe,hFae,hFb⟩ := finite_uniform_gluing U hU
    (fun j : t => O j) (fun j => hO j) E (fun a j => f a j)
    (fun a j => hf a j) (fun a j => hae a j)
    (fun j => B j) (fun j => hB j) data hdata (fun a j => hbound a j)
  refine ⟨V,∑ j : t, B j,F,isOpen_iUnion (fun j => hO j),hc,
    Finset.sum_nonneg (fun j _ => hB j),?_,hFc,hFae,hFb⟩
  exact ⟨t,Finset.sum_coe_sort t B⟩

end OQ14.Packet05PhaseCoverBound
#print axioms OQ14.Packet05PhaseCoverBound.finite_uniform_gluing
#print axioms OQ14.Packet05PhaseCoverBound.compact_uniform_gluing
