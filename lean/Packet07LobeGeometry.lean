import Packet07BinaryAssembly

/-! Each rounded double-cone component splits into two disjoint sign lobes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07LobeGeometry
open Set Metric
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)

def lobe (n : ℕ) (i : ι) (up : Bool) : Set Space :=
  CommonBinaryInterface.component p a center n i ∩
    {x | if up then center i 2 < x 2 else x 2 < center i 2}

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem lobe_open (n : ℕ) (i : ι) (up : Bool) : IsOpen (lobe p a center n i up) := by
  unfold lobe
  apply IsOpen.inter (CommonBinaryInterface.component_open p a center n i)
  cases up <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact isOpen_lt (EuclideanSpace.proj 2).continuous continuous_const
  · exact isOpen_lt continuous_const (EuclideanSpace.proj 2).continuous

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem lobe_split (n : ℕ) (i : ι) (x : Space) :
    x ∈ CommonBinaryInterface.component p a center n i ↔
      x ∈ lobe p a center n i false ∨ x ∈ lobe p a center n i true := by
  constructor
  · intro hx
    have hm := (ConicalJunctionPhysical.slope_properties (p i).threshold
      (p i).threshold_pos (p i).threshold_lt_one).1
    have hc := ConicalSmoothJunction.inclusion_subset n (ConicalJunctionPhysical.slope (p i).threshold) (a i) hm hx
    have hcone : ConicalJunctionPhysical.slope (p i).threshold *
      ‖ConicalJunctionPhysical.horizontal (x-center i)‖ < |(x-center i) 2| := hc.1
    have hpos : 0 < |(x-center i) 2| := lt_of_le_of_lt (mul_nonneg hm.le (norm_nonneg _)) hcone
    have hne : (x-center i) 2 ≠ 0 := abs_pos.mp hpos
    simp only [PiLp.sub_apply, sub_ne_zero] at hne
    rcases lt_or_gt_of_ne hne with hl | hr
    · exact Or.inl ⟨hx, hl⟩
    · exact Or.inr ⟨hx, hr⟩
  · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx

omit [Fintype ι] [Nonempty ι] in
theorem lobes_pairwise_disjoint (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i) (n : ℕ) :
    ∀ i j : ι × Bool, i ≠ j → Disjoint (lobe p a center n i.1 i.2) (lobe p a center n j.1 j.2) := by
  intro ⟨i, u⟩ ⟨j, v⟩ hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases h : i = j
  · subst j
    have huv : u ≠ v := by intro hv; subst v; exact hij rfl
    cases u <;> cases v <;> simp_all [lobe] <;> linarith
  · exact (Set.disjoint_left.mp (Packet07BinaryAssembly.component_pairwise_disjoint p a center ha hsep ha0 n i j h)) hx.1 hy.1

end OQ14.Packet07LobeGeometry
#print axioms OQ14.Packet07LobeGeometry.lobe_open
#print axioms OQ14.Packet07LobeGeometry.lobe_split
#print axioms OQ14.Packet07LobeGeometry.lobes_pairwise_disjoint
