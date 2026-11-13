import Packet06ConcreteModalRounding
import CommonBinaryCollar

/-! On a fixed annulus around a modal cone, the eventual rounded body is
literally the fixed sharp cone, uniformly throughout the whole annulus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RoundedFixedCollar
open Set Filter Metric Maxwell Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_body_annulus {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r ≤ ‖x-g.center i‖ → ‖x-g.center i‖ ≤ b →
      (x ∈ body g j ↔ ConicalJunctionPhysical.split (x-g.center i) ∈
        ConicalSmoothCapGraph.sharpCone (ConicalJunctionPhysical.slope g.datum.threshold)) := by
  classical
  have hpos : 0 < n^2 := sq_pos_of_pos (by linarith : 0 < n)
  have he := CommonBinaryCollar.eventually_annuli_agree (fun _ : Fin N => g.datum)
    (fun _ => g.radius) g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le)
    (fun _ => g.radius_outer) g.outer_disjoint (fun _ => g.radius_pos)
    (fun _ => r) (fun _ => b) (fun _ => hr) (fun _ => hb)
  filter_upwards [he] with j hj i x hlow hhigh
  have hxout : x ∈ ConicalCommonMaterial.outer (fun _ : Fin N => g.datum) g.center i := by
    change x ∈ closedBall (g.center i) g.datum.cutoff.rOut
    simp only [mem_closedBall,dist_eq_norm]
    exact hhigh.trans (hb.le.trans g.radius_outer)
  have hxzero : x-g.center i ≠ 0 := by
    intro h
    simp [h] at hlow
    linarith
  have hxlt : ‖x-g.center i‖ < g.radius := hhigh.trans_lt hb
  have hbody := CommonBinaryInterface.coefficient_body (fun _ : Fin N => g.datum)
    (fun _ => g.radius) g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le)
    (fun _ => g.radius_pos) (fun _ => g.radius_outer) g.outer_disjoint (n^2)
    (fun _ => g.contrast) j x
  have hlocal := ConicalCommonMaterial.coefficient_local (fun _ : Fin N => g.datum)
    (fun _ => g.radius) g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le)
    (fun _ => g.radius_outer) g.outer_disjoint i x hxout
  have hsharp := ConicalJunctionPhysical.original_binary g.datum g.radius g.radius_outer
    (x-g.center i) hxzero (ne_of_lt hxlt)
  have hvalue := hj i x hlow hhigh
  rw [hbody,hlocal] at hvalue
  change (if x ∈ body g j then n^2 else 0) =
    (ConicalSeparatedSource.material g.datum g.radius).value (VectorFourier.coordinateMap (x-g.center i)) at hvalue
  rw [hsharp,g.contrast] at hvalue
  simp only [hxlt,and_true] at hvalue
  by_cases h1 : x ∈ body g j <;>
    by_cases h2 : ConicalJunctionPhysical.split (x-g.center i) ∈
      ConicalSmoothCapGraph.sharpCone (ConicalJunctionPhysical.slope g.datum.threshold) <;>
    simp_all

end OQ14.Packet05RoundedFixedCollar
#print axioms OQ14.Packet05RoundedFixedCollar.eventually_body_annulus
