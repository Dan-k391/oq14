import CavityBallBridges
import FiniteRadialPartition

/-! # Actual finite radial layers around separated inclusions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace OQ14.LayeredInclusionCells

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open OQ14.CavityBallGeometry OQ14.CavityBallBridges
open scoped Topology

def cell {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) : ι ⊕ Fin (n+2) → Set Space
  | .inl i => ball (center i) (radius i)
  | .inr j => if j = 0 then cavity center radius (r 0) else FiniteRadialPartition.cell r j

theorem cell_radial_zero {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) : cell center radius r (.inr 0) = cavity center radius (r 0) := by
  simp [cell]

theorem cell_radial_ne_zero {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (j : Fin (n+2)) (hj : j ≠ 0) :
    cell center radius r (.inr j) = FiniteRadialPartition.cell r j := by
  simp only [cell,if_neg hj]

theorem cell_open {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (i : ι ⊕ Fin (n+2)) :
    IsOpen (cell center radius r i) := by
  rcases i with i | j
  · exact isOpen_ball
  · by_cases hj : j = 0
    · subst j
      rw [cell_radial_zero]
      exact cavity_isOpen center radius (r 0)
    · rw [cell_radial_ne_zero center radius r j hj]
      exact FiniteRadialPartition.cell_open r hm j

theorem cell_preconnected {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j)
    (hr : ∀ i, 0 ≤ radius i) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i : ι ⊕ Fin (n+2)) : IsPreconnected (cell center radius r i) := by
  rcases i with i | j
  · exact (convex_ball (center i) (radius i)).isPreconnected
  · by_cases hj : j = 0
    · subst j
      rw [cell_radial_zero]
      exact (cavity_isConnected center radius (r 0) (hp 0) hr hcore hsep).isPreconnected
    · rw [cell_radial_ne_zero center radius r j hj]
      exact FiniteRadialPartition.cell_preconnected r hm hp j

theorem ae_cell_cover {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r) :
    ∀ᵐ x : Space, ∃ i, x ∈ cell center radius r i := by
  filter_upwards [FiniteRadialPartition.ae_cell_cover r hm,
    DisjointBallCells.ae_cell_cover center radius] with x hx hball
  obtain ⟨j,hj⟩ := hx
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨i,hi⟩ := hball
    cases i with
    | some i => exact ⟨.inl i,hi⟩
    | none =>
      refine ⟨.inr 0,?_⟩
      rw [cell_radial_zero]
      rw [FiniteRadialPartition.cell_zero r hm] at hj
      exact ⟨hj,hi⟩
  · exact ⟨.inr j,by rwa [cell_radial_ne_zero center radius r j hj0]⟩

theorem radial_adjacent_bridge {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j)
    (hcore : ∀ i, ‖center i‖+radius i < r 0) (i : Fin (n+1)) :
    Bridge (cell center radius r (.inr i.castSucc)) (cell center radius r (.inr i.succ)) := by
  have hs0 : i.succ ≠ 0 := Fin.ne_of_val_ne (by simp)
  rw [cell_radial_ne_zero center radius r i.succ hs0]
  by_cases hi0 : i.val = 0
  · have hc0 : i.castSucc = 0 := Fin.ext hi0
    rw [hc0,cell_radial_zero]
    by_cases hn : i.val = n
    · have hsL : i.succ = Fin.last (n+1) := Fin.ext (by simp; omega)
      rw [hsL,FiniteRadialPartition.cell_last r hm]
      have hr0 : r (Fin.last n) = r 0 := congrArg r (Fin.ext (by simp; omega))
      rw [hr0]
      apply RadialMaterialCells.bridge_mono
        (cavity_shell_bridge center radius (r 0) (r 0+1) (hp 0) (by linarith) hcore)
        (Subset.refl _) _
      exact fun x hx => hx.1
    · rw [FiniteRadialPartition.cell_middle r hm i.succ (by simp) (by simp; omega)]
      change Bridge (cavity center radius (r 0))
        (RadialMaterialCells.annulus (r i) (r ⟨i.val+1,by omega⟩))
      have hi : i = 0 := Fin.ext hi0
      rw [show r i = r 0 from congrArg r hi]
      exact cavity_shell_bridge center radius (r 0) (r ⟨i.val+1,by omega⟩) (hp 0)
        (hm (by change 0 < i.val+1; omega)) hcore
  · have hc0 : i.castSucc ≠ 0 := Fin.ne_of_val_ne hi0
    rw [cell_radial_ne_zero center radius r i.castSucc hc0]
    exact FiniteRadialPartition.adjacent_bridge r hm hp i

theorem radial_reachable_from_zero {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j)
    (hcore : ∀ i, ‖center i‖+radius i < r 0) (j : Fin (n+2)) :
    Relation.ReflTransGen (fun i j => Bridge (cell center radius r i)
      (cell center radius r j)) (.inr 0) (.inr j) := by
  have h : ∀ m : ℕ, ∀ hm : m < n+2,
      Relation.ReflTransGen (fun i j => Bridge (cell center radius r i)
        (cell center radius r j)) (.inr 0) (.inr ⟨m,hm⟩) := by
    intro m
    induction m with
    | zero => intro hzero; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hsucc
      exact (ih (by omega)).tail (radial_adjacent_bridge center radius r hm hp hcore ⟨m,by omega⟩)
  exact h j.val j.isLt

theorem cells_reachable {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j)
    (hr : ∀ i, 0 < radius i) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i j : ι ⊕ Fin (n+2)) :
    Relation.ReflTransGen (fun i j => Bridge (cell center radius r i)
      (cell center radius r j)) i j := by
  let C := cell center radius r
  have hto (a : ι ⊕ Fin (n+2)) :
      Relation.ReflTransGen (fun i j => Bridge (C i) (C j)) a (.inr 0) := by
    rcases a with a | b
    · exact Relation.ReflTransGen.single
        (inclusion_cavity_bridge center radius (r 0) hr hcore hsep a)
    · exact reachable_symm C (radial_reachable_from_zero center radius r hm hp hcore b)
  exact (hto i).trans (reachable_symm C (hto j))

theorem exterior_seed {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j) (R : ℝ) :
    ∃ x ∈ cell center radius r (.inr (Fin.last (n+1))), R < ‖x‖ := by
  obtain ⟨x,hx,hR⟩ := FiniteRadialPartition.exists_exterior_seed r hm hp R
  refine ⟨x,?_,hR⟩
  rwa [cell_radial_ne_zero center radius r (Fin.last (n+1))
    (Fin.ne_of_val_ne (by simp))]

def partition {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ j, 0 < r j)
    (hr : ∀ i, 0 < radius i) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (ε : Space → ℝ) (value : ι ⊕ Fin (n+2) → ℝ) (hvalue : ∀ i, 0 < value i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell center radius r i → ε x = value i) :
    PiecewiseMaxwellUniqueness.Partition (ι ⊕ Fin (n+2)) ε where
  cell := cell center radius r
  region_open := cell_open center radius r hm
  region_preconnected := cell_preconnected center radius r hm hp (fun i => (hr i).le) hcore hsep
  value := value
  positive := hvalue
  constant_on := hε
  cover := ae_cell_cover center radius r hm
  reachable := cells_reachable center radius r hm hp hr hcore hsep

end OQ14.LayeredInclusionCells

#print axioms OQ14.LayeredInclusionCells.cell_radial_zero
#print axioms OQ14.LayeredInclusionCells.cell_radial_ne_zero
#print axioms OQ14.LayeredInclusionCells.cell_open
#print axioms OQ14.LayeredInclusionCells.cell_preconnected
#print axioms OQ14.LayeredInclusionCells.ae_cell_cover
#print axioms OQ14.LayeredInclusionCells.radial_adjacent_bridge
#print axioms OQ14.LayeredInclusionCells.radial_reachable_from_zero
#print axioms OQ14.LayeredInclusionCells.cells_reachable
#print axioms OQ14.LayeredInclusionCells.exterior_seed
#print axioms OQ14.LayeredInclusionCells.partition
