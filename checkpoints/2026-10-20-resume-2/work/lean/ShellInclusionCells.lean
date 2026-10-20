import CavityBallBridges
import PiecewiseMaxwellUniqueness

/-! # Concrete cells for separated inclusions enclosed by a spherical shell -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.ShellInclusionCells

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open OQ14.DisjointBallGeometry OQ14.CavityBallGeometry OQ14.CavityBallBridges
open scoped Topology

def cell {ι : Type*} (center : ι → Space) (radius : ι → ℝ) (L U : ℝ) :
    ι ⊕ Fin 3 → Set Space
  | .inl i => ball (center i) (radius i)
  | .inr j => ![cavity center radius L,
      OQ14.RadialMaterialCells.annulus L U,OQ14.RadialMaterialCells.exterior U] j

theorem cell_open {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L U : ℝ) (i : ι ⊕ Fin 3) : IsOpen (cell center radius L U i) := by
  rcases i with i | j
  · exact isOpen_ball
  · fin_cases j
    · exact cavity_isOpen center radius L
    · exact OQ14.RadialMaterialCells.annulus_open L U
    · exact OQ14.RadialMaterialCells.exterior_open U

theorem cell_preconnected {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L U : ℝ) (hL : 0 < L) (hLU : L < U) (hr : ∀ i, 0 ≤ radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i : ι ⊕ Fin 3) : IsPreconnected (cell center radius L U i) := by
  rcases i with i | j
  · exact (convex_ball (center i) (radius i)).isPreconnected
  · fin_cases j
    · exact (cavity_isConnected center radius L hL hr hcore hsep).isPreconnected
    · exact OQ14.RadialMaterialCells.annulus_preconnected L U hL.le
    · exact OQ14.RadialMaterialCells.exterior_preconnected U (hL.trans hLU).le

theorem ae_cell_cover {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L U : ℝ) : ∀ᵐ x : Space, ∃ i, x ∈ cell center radius L U i := by
  classical
  filter_upwards [OQ14.DisjointBallCells.ae_cell_cover center radius,
    OQ14.RadialMaterialCells.ae_norm_ne L,OQ14.RadialMaterialCells.ae_norm_ne U]
    with x hx hxL hxU
  obtain ⟨i,hi⟩ := hx
  cases i with
  | some i => exact ⟨.inl i,hi⟩
  | none =>
    by_cases hL : ‖x‖ < L
    · exact ⟨.inr 0,mem_ball_zero_iff.mpr hL,hi⟩
    · have hL' : L < ‖x‖ := lt_of_le_of_ne (not_lt.mp hL) (Ne.symm hxL)
      by_cases hU : ‖x‖ < U
      · exact ⟨.inr 1,hL',hU⟩
      · exact ⟨.inr 2,lt_of_le_of_ne (not_lt.mp hU) (Ne.symm hxU)⟩

theorem cells_reachable {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L U : ℝ) (hL : 0 < L) (hLU : L < U) (hr : ∀ i, 0 < radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i j : ι ⊕ Fin 3) :
    Relation.ReflTransGen (fun i j => Bridge (cell center radius L U i)
      (cell center radius L U j)) i j := by
  let C := cell center radius L U
  have h01 : Relation.ReflTransGen (fun i j => Bridge (C i) (C j)) (.inr 0) (.inr 1) :=
    Relation.ReflTransGen.single (cavity_shell_bridge center radius L U hL hLU hcore)
  have h12 : Relation.ReflTransGen (fun i j => Bridge (C i) (C j)) (.inr 1) (.inr 2) :=
    Relation.ReflTransGen.single (OQ14.RadialMaterialCells.annulus_exterior_bridge L U hL.le hLU)
  have hto (a : ι ⊕ Fin 3) : Relation.ReflTransGen (fun i j => Bridge (C i) (C j)) a (.inr 0) := by
    rcases a with a | b
    · exact Relation.ReflTransGen.single (inclusion_cavity_bridge center radius L hr hcore hsep a)
    · fin_cases b
      · exact Relation.ReflTransGen.refl
      · exact reachable_symm C h01
      · exact (reachable_symm C h12).trans (reachable_symm C h01)
  exact (hto i).trans (reachable_symm C (hto j))

theorem exterior_seed {ι : Type*} (center : ι → Space) (radius : ι → ℝ)
    (L U R : ℝ) : ∃ x ∈ cell center radius L U (.inr 2), R < ‖x‖ := by
  let b := |U|+|R|+1
  have hb : 0 < b := by dsimp [b]; positivity
  have hn : ‖OQ14.RadialMaterialCells.axis b‖ = b := by
    rw [OQ14.RadialMaterialCells.axis_norm,abs_of_pos hb]
  refine ⟨OQ14.RadialMaterialCells.axis b,?_,?_⟩
  · change U < ‖OQ14.RadialMaterialCells.axis b‖
    rw [hn]
    dsimp [b]
    linarith [le_abs_self U,abs_nonneg R]
  · rw [hn]
    dsimp [b]
    linarith [le_abs_self R,abs_nonneg U]

def partition {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L U : ℝ) (hL : 0 < L) (hLU : L < U) (hr : ∀ i, 0 < radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (ε : Space → ℝ) (value : ι ⊕ Fin 3 → ℝ) (hvalue : ∀ i, 0 < value i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell center radius L U i → ε x = value i) :
    OQ14.PiecewiseMaxwellUniqueness.Partition (ι ⊕ Fin 3) ε where
  cell := cell center radius L U
  region_open := cell_open center radius L U
  region_preconnected := cell_preconnected center radius L U hL hLU (fun i => (hr i).le) hcore hsep
  value := value
  positive := hvalue
  constant_on := hε
  cover := ae_cell_cover center radius L U
  reachable := cells_reachable center radius L U hL hLU hr hcore hsep

end OQ14.ShellInclusionCells

#print axioms OQ14.ShellInclusionCells.cell_open
#print axioms OQ14.ShellInclusionCells.cell_preconnected
#print axioms OQ14.ShellInclusionCells.ae_cell_cover
#print axioms OQ14.ShellInclusionCells.cells_reachable
#print axioms OQ14.ShellInclusionCells.exterior_seed
#print axioms OQ14.ShellInclusionCells.partition
