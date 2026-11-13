import Packet05FiniteCollarBound
import Packet05ActualMaximum

/-! A fixed finite cover turns local component bounds into one actual
Euclidean-amplitude collar bound, independent of the family index. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05FinitePhysicalCollar
open MeasureTheory Set Filter Metric Maxwell Packet05ActualMaximum
open scoped Topology

theorem amplitude_bound (E : Fin 3 → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, ‖E i‖ ≤ B) : Real.sqrt (∑ i : Fin 3, ‖E i‖^2) ≤ 3*B := by
  have hsq (i : Fin 3) : ‖E i‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  have hsum : (∑ i : Fin 3, ‖E i‖^2) ≤ 3*B^2 := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hsq i)
  have hn : 0 ≤ ∑ i : Fin 3, ‖E i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have hh := Real.sqrt_nonneg (∑ i : Fin 3, ‖E i‖^2)
  nlinarith

theorem finite_physical_collar (center : Space) (r R : ℝ) (hr : r < R)
    (E : ℕ → Fin 3 → Space → ℂ)
    (hlocal : ∀ x ∈ sphere center r, ∃ O : Set Space, ∃ B : ℝ,
      IsOpen O ∧ x ∈ O ∧ 0 ≤ B ∧
      ∀ᶠ j : ℕ in atTop, ∀ᵐ y ∂volume, y ∈ O → ∀ i, ‖E j i y‖ ≤ B) :
    ∃ A : Set Space, ∃ B : ℝ, IsOpen A ∧ A ⊆ ball center R ∧
      sphere center r ⊆ A ∧ 0 ≤ B ∧
      ∀ᶠ j : ℕ in atTop, ∀ᵐ y ∂volume.restrict A, physicalAmplitude (E j) y ≤ B := by
  classical
  let J := {x : Space // x ∈ sphere center r}
  choose O B hO hx hB hb using fun x : J => hlocal x x.property
  have hcover : sphere center r ⊆ ⋃ x : J, O x := by
    intro x hx'
    exact mem_iUnion.mpr ⟨⟨x,hx'⟩,hx ⟨x,hx'⟩⟩
  have hloc (x : J) : ∀ᶠ j : ℕ in atTop, ∀ᵐ y ∂volume,
      y ∈ O x → ‖((physicalAmplitude (E j) y : ℝ) : ℂ)‖ ≤ 3*B x := by
    filter_upwards [hb x] with j hj
    filter_upwards [hj] with y hy hyO
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ physicalAmplitude (E j) y from Real.sqrt_nonneg _)]
    exact amplitude_bound _ _ (hB x) (hy hyO)
  obtain ⟨V,C,hV,hKV,hC,hbound⟩ := Packet05FiniteCollarBound.compact_eventual_ae_bound
    (sphere center r) (isCompact_sphere center r) O hO hcover (fun j y => ((physicalAmplitude (E j) y : ℝ) : ℂ))
    (fun x => 3*B x) hloc
  let A := V ∩ ball center R
  have hKA : sphere center r ⊆ A := by
    intro x hx'
    exact ⟨hKV hx', by simpa only [mem_sphere,mem_ball] using (show dist x center < R by rw [hx']; exact hr)⟩
  refine ⟨A,C,hV.inter isOpen_ball,inter_subset_right,hKA,hC,?_⟩
  filter_upwards [hbound] with j hj
  apply (ae_restrict_iff' (hV.inter isOpen_ball).measurableSet).mpr
  filter_upwards [hj] with y hy hyA
  have h := hy hyA.1
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ physicalAmplitude (E j) y from Real.sqrt_nonneg _)] using h

end OQ14.Packet05FinitePhysicalCollar
#print axioms OQ14.Packet05FinitePhysicalCollar.amplitude_bound
#print axioms OQ14.Packet05FinitePhysicalCollar.finite_physical_collar
