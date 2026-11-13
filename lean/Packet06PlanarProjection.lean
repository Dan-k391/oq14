import Packet06PlacedPeaks
import Packet07PlanarCenters
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlanarProjection
open Metric Set OQ14.Maxwell OQ14.Packet06CyclicRotation
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def project (x : Maxwell.Space) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0,x 1]

theorem project_embed (u : Plane) : project (Packet07PlanarCenters.planeEmbed u)=u := by
  ext i
  fin_cases i <;> rfl

theorem norm_project_le (x : Maxwell.Space) : ‖project x‖ ≤ ‖x‖ := by
  have he : ‖project x‖^2 = (x 0)^2+(x 1)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [project,Fin.sum_univ_two]
  have hx : ‖x‖^2=(x 0)^2+(x 1)^2+(x 2)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 2),norm_nonneg (project x),norm_nonneg x]

theorem project_ball (u : Plane) (r : ℝ) (x : Maxwell.Space)
    (hx : x ∈ ball (Packet07PlanarCenters.planeEmbed u) r) : project x ∈ ball u r := by
  rw [mem_ball,dist_eq_norm]
  have he : project x-u = project (x-Packet07PlanarCenters.planeEmbed u) := by
    ext i
    fin_cases i <;> simp [project,Packet07PlanarCenters.planeEmbed,PiLp.sub_apply]
  rw [he]
  exact (norm_project_le _).trans_lt (by simpa only [mem_ball,dist_eq_norm] using hx)

theorem point_axial_planar (s : ℝ) (a x : Maxwell.Space) (ha : a 2=0)
    (hx : x 0=0 ∧ x 1=0) : Packet06PhysicalPlacement.point s a x 2=0 := by
  simp [Packet06PhysicalPlacement.point,rotate,OQ14.WeakCurl.previous,ha,hx.2]
theorem placed_centers_in_patch {N : ℕ} (P : Set Plane) (u : Plane) (r target : ℝ)
    (hr : 0 < r) (htarget : 0 < target) (hP : ball u r ⊆ P)
    (z₀ z : ℂ) (hz₀ : 0 < z₀.re) (hz : 0 < z.re)
    (hclose : |z.re-z₀.re| < z₀.re/2) (center : Fin N → Maxwell.Space)
    (haxis : ∀ i, center i 0 = 0 ∧ center i 1 = 0) (hinj : Function.Injective center)
    (hcluster : ∀ i, center i ∈ ball 0 (r*target/(2*z₀.re))) :
    let s := target/z.re
    let a := Packet07PlanarCenters.planeEmbed u
    (∀ i, (Packet06PhysicalPlacement.point s a (center i)) 2 = 0 ∧
      project (Packet06PhysicalPlacement.point s a (center i)) ∈ P) ∧
      Function.Injective (fun i => Packet06PhysicalPlacement.point s a (center i)) := by
  dsimp only
  constructor
  · intro i
    refine ⟨point_axial_planar _ _ _ (Packet07PlanarCenters.planeEmbed_coord u) (haxis i),?_⟩
    apply hP
    apply project_ball
    exact Packet06PhysicalPlacement.frequency_cluster target r htarget hr z₀ z hz₀ hz hclose _ _ (hcluster i)
  · intro i j hij
    apply hinj
    have hh := congrArg (fun x => unrotate ((target/z.re) • (x-Packet07PlanarCenters.planeEmbed u))) hij
    simp only at hh
    change unrotate ((target/z.re) • (Packet06PhysicalPlacement.point (target/z.re) (Packet07PlanarCenters.planeEmbed u) (center i)-Packet07PlanarCenters.planeEmbed u)) =
      unrotate ((target/z.re) • (Packet06PhysicalPlacement.point (target/z.re) (Packet07PlanarCenters.planeEmbed u) (center j)-Packet07PlanarCenters.planeEmbed u)) at hh
    rw [Packet06PlacedPeaks.inverse_point _ (div_pos htarget hz),Packet06PlacedPeaks.inverse_point _ (div_pos htarget hz)] at hh
    exact hh
theorem inverse_point_right (s : ℝ) (hs : 0 < s) (a y : Maxwell.Space) :
    Packet06PhysicalPlacement.point s a (unrotate (s • (y-a))) = y := by
  simp only [Packet06PhysicalPlacement.point, ← rotation.map_smul, rotate_unrotate,
    smul_smul,inv_mul_cancel₀ hs.ne',one_smul,add_sub_cancel]

theorem point_distance_pair (s : ℝ) (hs : 0 < s) (a x y : Maxwell.Space) :
    dist (Packet06PhysicalPlacement.point s a x) (Packet06PhysicalPlacement.point s a y) = s⁻¹*dist x y := by
  have hrot : rotate (x-y) = rotate x-rotate y := rotation.map_sub x y
  simp only [dist_eq_norm,Packet06PhysicalPlacement.point,add_sub_add_left_eq_sub,← smul_sub,← hrot,
    norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),rotate_norm]

theorem point_ball_iff (s : ℝ) (hs : 0 < s) (a center y : Maxwell.Space) (r : ℝ) :
    y ∈ ball (Packet06PhysicalPlacement.point s a center) (r/s) ↔
      unrotate (s • (y-a)) ∈ ball center r := by
  let x := unrotate (s • (y-a))
  have hx : Packet06PhysicalPlacement.point s a x = y := inverse_point_right s hs a y
  change y ∈ ball (Packet06PhysicalPlacement.point s a center) (r/s) ↔ x ∈ ball center r
  rw [← hx,mem_ball,point_distance_pair s hs a x center,div_eq_mul_inv,mem_ball]
  have he : r*s⁻¹ = s⁻¹*r := by ring
  rw [he]
  exact (mul_lt_mul_left (inv_pos.mpr hs))

#print axioms OQ14.Packet06PlanarProjection.project_embed
#print axioms OQ14.Packet06PlanarProjection.norm_project_le
#print axioms OQ14.Packet06PlanarProjection.project_ball
#print axioms OQ14.Packet06PlanarProjection.point_axial_planar
#print axioms OQ14.Packet06PlanarProjection.placed_centers_in_patch
#print axioms OQ14.Packet06PlanarProjection.inverse_point_right
#print axioms OQ14.Packet06PlanarProjection.point_distance_pair
#print axioms OQ14.Packet06PlanarProjection.point_ball_iff
end OQ14.Packet06PlanarProjection
