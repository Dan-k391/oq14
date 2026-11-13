import Packet07PlanarCenters

/-! Uniform positive geometric clearance for any finite family of distinct centers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07FiniteSeparation
open Set Metric

/-- A finite family of positive real numbers has a common strictly positive lower bound. -/
theorem finite_positive_lower {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x s hx ih =>
    have hxpos : 0 < f x := hf x (Finset.mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 < f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨ε, hε, hsmall⟩ := ih hs
    refine ⟨min ε (f x / 2), lt_min hε (half_pos hxpos), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have := min_le_right ε (f i / 2)
      linarith
    · exact lt_of_le_of_lt (min_le_left _ _) (hsmall i hi)

/-- A finite injective family has a common positive radius whose fourfold
    value is strictly smaller than every distinct-center distance. -/
theorem separated_radius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Maxwell.Space) (hinj : Function.Injective center) :
    ∃ a : ℝ, 0 < a ∧ ∀ i j, i ≠ j → 4*a < dist (center i) (center j) := by
  let f : ι × ι → ℝ := fun ij => if ij.1 = ij.2 then 1 else dist (center ij.1) (center ij.2)
  have hf : ∀ z ∈ (Finset.univ : Finset (ι × ι)), 0 < f z := by
    intro ⟨i,j⟩ _
    by_cases hij : i = j
    · simp [f, hij]
    · simp only [f, hij, ↓reduceIte]
      exact dist_pos.mpr (fun h => hij (hinj h))
  obtain ⟨ε,hε,hsmall⟩ := finite_positive_lower Finset.univ f hf
  refine ⟨ε/4, by positivity, ?_⟩
  intro i j hij
  have hh := hsmall (i,j) (Finset.mem_univ _)
  simp only [f, hij, ↓reduceIte] at hh
  linarith

/-- The radius from the finite separation theorem gives disjoint closed outer balls. -/
theorem disjoint_outer_balls {ι : Type*} (center : ι → Maxwell.Space) (a : ℝ)
    (hsep : ∀ i j, i ≠ j → 4*a < dist (center i) (center j)) :
    ∀ i j, i ≠ j → Disjoint (closedBall (center i) (2*a)) (closedBall (center j) (2*a)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h1 : dist x (center i) ≤ 2*a := hx
  have h2 : dist x (center j) ≤ 2*a := hy
  have ht := dist_triangle (center i) x (center j)
  rw [dist_comm (center i) x] at ht
  linarith [hsep i j hij]

/-- Separated conical tips have disjoint smaller peak balls. -/
theorem disjoint_peak_balls {ι : Type*} (center : ι → Maxwell.Space) (a : ℝ) (ha : 0 ≤ a)
    (hsep : ∀ i j, i ≠ j → a+a < dist (center i) (center j)) :
    ∀ i j, i ≠ j → Disjoint (ball (center i) (a/2)) (ball (center j) (a/2)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h1 : dist x (center i) < a/2 := hx
  have h2 : dist x (center j) < a/2 := hy
  have ht := dist_triangle (center i) x (center j)
  rw [dist_comm (center i) x] at ht
  linarith [hsep i j hij]

end OQ14.Packet07FiniteSeparation
#print axioms OQ14.Packet07FiniteSeparation.finite_positive_lower
#print axioms OQ14.Packet07FiniteSeparation.separated_radius
#print axioms OQ14.Packet07FiniteSeparation.disjoint_outer_balls

#print axioms OQ14.Packet07FiniteSeparation.disjoint_peak_balls
