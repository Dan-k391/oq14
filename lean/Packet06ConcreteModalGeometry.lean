import Packet06ExcitationCenters
import Packet07CommonConeData

/-! A concrete fixed cone family chosen after the base sphere mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ConcreteModalGeometry
open Metric Set Maxwell Packet06MaterialSymmetry
abbrev Space := Maxwell.Space

structure Geometry (N : ℕ) (n : ℝ) where
  center : Fin N → Space
  datum : ConicalStaticVolume.Data
  radius : ℝ
  onAxis : Packet06ConeUnionSymmetry.OnAxis center
  injective : Function.Injective center
  contrast : datum.contrast=n^2
  threshold : datum.threshold=(3/4 : ℝ)
  singular : datum.exponent < 1
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  radius_inner : radius < datum.cutoff.rIn
  radius_outer : radius ≤ datum.cutoff.rOut
  outer_inside : ∀ i, closedBall (center i) datum.cutoff.rOut ⊆ ball 0 1
  outer_disjoint : ∀ i j, i ≠ j →
    Disjoint (closedBall (center i) datum.cutoff.rOut) (closedBall (center j) datum.cutoff.rOut)
  separated : ∀ i j, i ≠ j → radius+radius < dist (center i) (center j)

def cone {N : ℕ} {n : ℝ} (g : Geometry N n) : StaticCoefficient.Coefficient :=
  ConicalCommonMaterial.coefficient (fun _ => g.datum) (fun _ => g.radius) g.center
    (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer) g.outer_disjoint

theorem admissible {N : ℕ} {n : ℝ} (g : Geometry N n) :
    Axial (cone g) ∧ Meridional (cone g) ∧
    (∀ x : Space, x ∉ closedBall 0 1 → (cone g).value (VectorFourier.coordinateMap x)=0) := by
  refine ⟨Packet06ConeUnionSymmetry.literal_axial _ _ _ _ _ _ _ _ g.onAxis,
    Packet06ConeUnionSymmetry.literal_meridional _ _ _ _ _ _ _ _ g.onAxis,?_⟩
  exact ConicalCommonMaterial.coefficient_support _ _ _ _ _ _ _ _ 1
    (fun i => (g.outer_inside i).trans ball_subset_closedBall)

theorem exists_geometry (N : ℕ) (n : ℝ) (hn : 1 < n) (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) :
    ∃ g : Geometry N n, ∀ i, Packet06SphereLocalField.inner n z w (g.center i) 2 ≠ 0 := by
  obtain ⟨c,a,haxis,hi,ha,hinside,hsep,hfield⟩ :=
    Packet06ExcitationCenters.sphere_excitation_centers N n hn z w hz hw
  let χ : ContDiffBump (0 : Space) := ⟨a,2*a,ha,by linarith⟩
  obtain ⟨p,hχ,hcontrast,hthreshold,hν,_⟩ :=
    ConicalFamily.exists_data χ (n^2) (3/4) (by nlinarith) (by norm_num) (by norm_num)
  let r := min (a/2) (1/2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hra : r ≤ a/2 := min_le_left _ _
  let g : Geometry N n := {
    center := c
    datum := p
    radius := r
    onAxis := haxis
    injective := hi
    contrast := hcontrast
    threshold := hthreshold
    singular := hν
    radius_pos := hr
    radius_lt_one := (min_le_right _ _).trans_lt (by norm_num)
    radius_inner := by rw [hχ]; change r<a; linarith
    radius_outer := by rw [hχ]; change r≤2*a; linarith
    outer_inside := by rw [hχ]; exact hinside
    outer_disjoint := by rw [hχ]; exact Packet07FiniteSeparation.disjoint_outer_balls c a hsep
    separated := by intro i j hij; linarith [hsep i j hij] }
  refine ⟨g,?_⟩
  intro i
  exact hfield i (c i) (by simp [ha.le])

end OQ14.Packet06ConcreteModalGeometry
#print axioms OQ14.Packet06ConcreteModalGeometry.admissible
#print axioms OQ14.Packet06ConcreteModalGeometry.exists_geometry
