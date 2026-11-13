import Packet07DrivenUniformAtlas

/-! Finite fixed C⁴ material charts for a compact subset of one actual modal
annulus, with all material laws valid eventually in the rounded family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformFiniteAtlas
open Set Filter Metric Maxwell Packet07PlanarSetup Packet07DrivenUniformCollarChart
  Packet07DrivenUniformAtlas Packet05ChartBasis Packet05GraphChartMap
  Packet05PhysicalGraphChart Packet05PhysicalChartBranches
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

structure Chart {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ} (g : Setup N Pset d t) where
  up : Bool
  axis : Fin 3
  graph : Plane → ℝ
  flat : Set Space
  body : Set Space
  host : ℂ
  jump : ℝ
  regular : ContDiff ℝ 4 graph
  compact : HasCompactSupport graph
  flat_open : IsOpen flat
  host_ne : host ≠ 0
  jump_nonneg : 0 ≤ jump
  maps_outer : ∀ y ∈ flat, inverseOriented up axis (graphMap (liftedHeight graph) y) ∈
    ball (0 : Space) (Packet07DrivenUniformAtlas.outer g).rIn
  side : ∀ y ∈ flat, inverseOriented up axis (graphMap (liftedHeight graph) y) ∈ body ↔ 0 < y 2
  material : ∀ᶠ j : ℕ in atTop, ∀ y ∈ flat,
    Packet06MaxwellScalarEquation.epsilon (g.rounded j)
      (inverseOriented up axis (graphMap (liftedHeight graph) y)) =
      host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight graph) y) ∈ body
        then (1+jump : ℂ) else 1)

def physical {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ} {g : Setup N Pset d t}
    (c : Chart g) : Set Space :=
  physicalFlatMap c.up c.axis c.graph ⁻¹' c.flat

theorem finite_fixed_atlas {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N Pset d t)
    (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) (i : Fin N)
    (K : Set Space) (hK : IsCompact K) (hKann : K ⊆ annulus g i r b) :
    ∃ j0 : ℕ, ∃ J : Finset (Chart g),
      (∀ᶠ j : ℕ in atTop, ∀ (k : Fin N) (x : Space),
        r < ‖x-g.centers k‖ → ‖x-g.centers k‖ < b → (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔ x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0)) ∧
      K ⊆ ⋃ c ∈ J, physical c ∧
      (∀ c ∈ J, IsOpen (physical c)) ∧
      ∀ᶠ j : ℕ in atTop, ∀ c ∈ J, ∀ y ∈ c.flat,
        Packet06MaxwellScalarEquation.epsilon (g.rounded j)
          (inverseOriented c.up c.axis (graphMap (liftedHeight c.graph) y)) =
          c.host * (by classical exact if inverseOriented c.up c.axis (graphMap (liftedHeight c.graph) y) ∈ c.body
            then (1+c.jump : ℂ) else 1) := by
  classical
  obtain ⟨j0,hstable,hatlas⟩ := actual_fixed_collar_atlas g r b hr hb
  let I := {x : Space // x ∈ annulus g i r b}
  have hex (x : I) : ∃ c : Chart g, x.1 ∈ physical c := by
    obtain ⟨up,axis,G,T,bodyChart,host,d,hG,hGc,hT,hxT,hhost,hd,hmap,hside,hmat⟩ := hatlas i x x.2
    exact ⟨⟨up,axis,G,T,bodyChart,host,d,hG,hGc,hT,hhost,hd,hmap,hside,hmat⟩,hxT⟩
  choose c hc using hex
  have hopen (x : I) : IsOpen (physical (c x)) :=
    (c x).flat_open.preimage (physicalFlat_continuous (c x).up (c x).axis (c x).graph
      ((c x).regular.of_le (by decide)))
  have hcover : K ⊆ ⋃ x : I, physical (c x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hKann hx⟩,hc ⟨x,hKann hx⟩⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : I => physical (c x)) hopen hcover
  let J : Finset (Chart g) := t.image c
  refine ⟨j0,J,hstable,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨c y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hxy⟩
  · intro cc hcc
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hcc
    exact hopen y
  · have hh : ∀ᶠ j : ℕ in atTop, ∀ cc : J, ∀ y ∈ cc.1.flat,
        Packet06MaxwellScalarEquation.epsilon (g.rounded j)
          (inverseOriented cc.1.up cc.1.axis (graphMap (liftedHeight cc.1.graph) y)) =
          cc.1.host * (if inverseOriented cc.1.up cc.1.axis (graphMap (liftedHeight cc.1.graph) y) ∈ cc.1.body
            then (1+cc.1.jump : ℂ) else 1) :=
      Filter.eventually_all.mpr (fun cc => cc.1.material)
    filter_upwards [hh] with j hj cc hcc y hy
    exact hj ⟨cc,hcc⟩ y hy

end OQ14.Packet07DrivenUniformFiniteAtlas
#print axioms OQ14.Packet07DrivenUniformFiniteAtlas.finite_fixed_atlas
