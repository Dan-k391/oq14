import Packet05ActualGraphForcing

/-! Local C³ graph data extend by an actual compact smooth cutoff, without
requiring any smoothness of the original graph outside its chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05GraphCompactExtensionC4
open Set Filter OQ14.ConicalSmoothJunction
open scoped Topology

def extendGraph (χ g : Plane → ℝ) : Plane → ℝ := fun x => χ x * g x

theorem extend_graph_regular_c4 (V : Set Plane) (hV : IsOpen V) (χ g : Plane → ℝ)
    (hχ : ContDiff ℝ 4 χ) (hχV : tsupport χ ⊆ V) (hg : ContDiffOn ℝ 4 g V) :
    ContDiff ℝ 4 (extendGraph χ g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hgx : ContDiffAt ℝ 4 g x := (hg x (hχV hx)).contDiffAt (hV.mem_nhds (hχV hx))
    exact hχ.contDiffAt.mul hgx
  · apply (contDiffAt_const : ContDiffAt ℝ 4 (fun _ : Plane => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [not_mem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change χ y * g y = 0
    rw [show χ y = 0 from hy]
    simp

theorem extend_graph_compact (χ g : Plane → ℝ) (hχ : HasCompactSupport χ) :
    HasCompactSupport (extendGraph χ g) := hχ.mul_right

theorem extend_graph_eq (χ g : Plane → ℝ) (U : Set Plane) (hχ : ∀ x ∈ U, χ x = 1) :
    ∀ x ∈ U, extendGraph χ g x = g x := by
  intro x hx
  simp [extendGraph,hχ x hx]

end OQ14.Packet05GraphCompactExtensionC4
#print axioms OQ14.Packet05GraphCompactExtensionC4.extend_graph_regular_c4
#print axioms OQ14.Packet05GraphCompactExtensionC4.extend_graph_compact
#print axioms OQ14.Packet05GraphCompactExtensionC4.extend_graph_eq
