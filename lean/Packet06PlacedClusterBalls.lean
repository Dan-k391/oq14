import Packet06PlanarProjection
import Packet06ConcreteModalGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlacedClusterBalls
open Metric Set OQ14.Maxwell OQ14.Packet06PlanarProjection OQ14.Packet06PhysicalPlacement
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06CyclicRotation
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem placed_balls {N : ℕ} {n : ℝ} (g : Geometry N n) (P : Set Plane) (u : Plane)
    (rp target : ℝ) (hrp : 0 < rp) (htarget : 0 < target) (hP : ball u rp ⊆ P)
    (z₀ z : ℂ) (hz₀ : 0 < z₀.re) (hz : 0 < z.re)
    (hclose : |z.re-z₀.re| < z₀.re/2)
    (hcluster : ∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 (rp*target/(2*z₀.re)))
    (r : ℝ) (_hr : 0 < r) (hrb : r ≤ g.radius) :
    let sc := target/z.re
    let a := Packet07PlanarCenters.planeEmbed u
    (∀ i, (point sc a (g.center i)) 2 = 0 ∧ project (point sc a (g.center i)) ∈ P) ∧
      Function.Injective (fun i => point sc a (g.center i)) ∧
      (∀ i y, y ∈ ball (point sc a (g.center i)) (r/sc) → project y ∈ P) ∧
      (∀ i j, i ≠ j → Disjoint (ball (point sc a (g.center i)) (r/sc))
        (ball (point sc a (g.center j)) (r/sc))) := by
  dsimp only
  let sc := target/z.re
  let a := Packet07PlanarCenters.planeEmbed u
  have hsc : 0 < sc := div_pos htarget hz
  have hcenter (i : Fin N) : g.center i ∈ ball 0 (rp*target/(2*z₀.re)) :=
    hcluster i (mem_closedBall_self g.datum.cutoff.rOut_pos.le)
  obtain ⟨hcenter',hinj⟩ := placed_centers_in_patch P u rp target hrp htarget hP z₀ z hz₀ hz hclose
    g.center g.onAxis g.injective hcenter
  refine ⟨hcenter',hinj,?_,?_⟩
  · intro i y hy
    let x := unrotate (sc • (y-a))
    have hx : x ∈ ball (g.center i) r := (point_ball_iff sc hsc a (g.center i) y r).mp hy
    have houter : x ∈ closedBall (g.center i) g.datum.cutoff.rOut :=
      (closedBall_subset_closedBall (hrb.trans g.radius_outer)) (ball_subset_closedBall hx)
    have hsmall := hcluster i houter
    have hplaced := frequency_cluster target rp htarget hrp z₀ z hz₀ hz hclose a x hsmall
    have he : point sc a x = y := inverse_point_right sc hsc a y
    rw [he] at hplaced
    exact hP (project_ball u rp y hplaced)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    have hsep := g.separated i j hij
    have hd := point_distance_pair sc hsc a (g.center i) (g.center j)
    have htri := dist_triangle (point sc a (g.center i)) y (point sc a (g.center j))
    have h1 : dist (point sc a (g.center i)) y < r/sc := by simpa [dist_comm] using hyi
    have h2 : dist y (point sc a (g.center j)) < r/sc := hyj
    rw [hd] at htri
    have hsep' : r+r < dist (g.center i) (g.center j) := lt_of_le_of_lt (add_le_add hrb hrb) hsep
    have hh := mul_lt_mul_of_pos_left hsep' (inv_pos.mpr hsc)
    rw [div_eq_mul_inv] at h1 h2
    nlinarith
#print axioms OQ14.Packet06PlacedClusterBalls.placed_balls
end OQ14.Packet06PlacedClusterBalls
