import DisjointBallCells
import PiecewiseMaxwellUniqueness

/-! # Concrete Maxwell partition adapter for separated balls -/

noncomputable section
set_option autoImplicit false

namespace OQ14.DisjointBallPartition

open MeasureTheory Metric Set OQ14.Maxwell
open OQ14.DisjointBallGeometry OQ14.DisjointBallCells

def partition {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (ε : Space → ℝ) (value : Option ι → ℝ) (hvalue : ∀ i, 0 < value i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell center radius i → ε x = value i) :
    OQ14.PiecewiseMaxwellUniqueness.Partition (Option ι) ε where
  cell := cell center radius
  region_open := cell_open center radius
  region_preconnected := cell_preconnected center radius (fun i => (hr i).le) hsep
  value := value
  positive := hvalue
  constant_on := hε
  cover := ae_cell_cover center radius
  reachable := cells_reachable center radius hr hsep

theorem exterior_seed {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (R : ℝ) : ∃ x ∈ cell center radius none, R < ‖x‖ :=
  exists_exterior_outside center radius R

end OQ14.DisjointBallPartition

#print axioms OQ14.DisjointBallPartition.partition
#print axioms OQ14.DisjointBallPartition.exterior_seed
