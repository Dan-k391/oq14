import Packet05FixedCollarChart

/-! A compact collar acquires one eventual uniform a.e. bound from its
fixed open local charts; the cover is chosen before the family index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FiniteCollarBound
open MeasureTheory Set Filter Maxwell
open scoped Topology

theorem compact_eventual_ae_bound {J : Type*} (K : Set Space) (hK : IsCompact K)
    (O : J → Set Space) (hO : ∀ j, IsOpen (O j)) (hcover : K ⊆ ⋃ j, O j)
    (E : ℕ → Space → ℂ) (B : J → ℝ)
    (hlocal : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂volume, x ∈ O j → ‖E n x‖ ≤ B j) :
    ∃ V : Set Space, ∃ C : ℝ, IsOpen V ∧ K ⊆ V ∧ 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂volume, x ∈ V → ‖E n x‖ ≤ C := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover O hO hcover
  let V : Set Space := ⋃ j : t, O j
  let C : ℝ := ∑ j : t, max (B j) 0
  have hKV : K ⊆ V := by
    intro x hx
    obtain ⟨j,hjt,hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨j,hjt⟩,hxj⟩
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have he : ∀ᶠ n : ℕ in atTop, ∀ j : t, ∀ᵐ x ∂volume, x ∈ O j → ‖E n x‖ ≤ B j :=
    Filter.eventually_all.mpr (fun j => hlocal j)
  refine ⟨V,C,isOpen_iUnion (fun j => hO j),hKV,hC,?_⟩
  filter_upwards [he] with n hn
  have hae : ∀ᵐ x ∂volume, ∀ j : t, x ∈ O j → ‖E n x‖ ≤ B j := ae_all_iff.mpr hn
  filter_upwards [hae] with x hx hxV
  obtain ⟨j,hj⟩ := mem_iUnion.mp hxV
  have hsum : max (B j) 0 ≤ C := by
    exact Finset.single_le_sum (f := fun k : t => max (B k) 0)
      (fun k _ => le_max_right _ _) (Finset.mem_univ j)
  exact (hx j hj).trans ((le_max_left _ _).trans hsum)

end OQ14.Packet05FiniteCollarBound
#print axioms OQ14.Packet05FiniteCollarBound.compact_eventual_ae_bound
