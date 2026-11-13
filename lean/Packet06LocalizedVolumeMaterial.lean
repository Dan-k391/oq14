import Packet06LocalizedVolumeState
import Packet06RigidMaterialShape
import Packet06PlacedMaterialGeometry

/-! Exact smooth three-value material for a localized mode after rigid framing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06LocalizedVolumeMaterial
open Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06LocalizedVolumeState Packet06PlacedKernel Packet06PlacementHomeomorph
  Packet06RigidHotspotState Packet06RigidHotspotFrame Packet06ModalHotspotExistence
abbrev Space := Maxwell.Space

theorem framed_material {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 < η) (j : ℕ)
    (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 z u=1)
    (r B : ℝ) (hrg : r < g.radius)
    (hhot : ∀ i, Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη.le j) z u (body g j) (g.center i) r 0 B)
    (s : ℝ) (hs : 0 < s) (a : Space) (ha : a 2=0)
    (hinner : SmoothBoundary (body g j)) (K : ℝ) (hK : 1 < K) (hceil : (1+η)*n^2 ≤ K^2)
    (θ φ : ℝ) (t : Space) :
    let d := initial n hn g η hη j z u hu hN r B hrg hhot s hs a ha
    let outer := placement s hs a '' ball (0 : Space) 1
    let out := Packet07DrivenRigidHotspot.placement θ φ t '' outer
    IsOpen out ∧ (transform θ φ t d).body ⊆ out ∧ SmoothBoundary (transform θ φ t d).body ∧ SmoothBoundary out ∧
    (∀ y, MaterialMaxwell.dielectric (transform θ φ t d).material y =
      (by classical exact if y ∈ (transform θ φ t d).body then (1+η)*n^2 else if y ∈ out then n^2 else 1)) ∧
    ∀ y, 1 ≤ MaterialMaxwell.dielectric (transform θ φ t d).material y ∧
      MaterialMaxwell.dielectric (transform θ φ t d).material y ≤ K^2 := by
  classical
  apply Packet06RigidMaterialShape.material_shape θ φ t _ _ n η K
  · exact (placement s hs a).isOpenMap _ isOpen_ball
  · exact Set.image_subset _ (body_inside g j)
  · exact Packet06PlacedSmoothBoundary.smooth_boundary_image s hs a _ hinner
  · exact Packet06PlacedMaterialGeometry.placed_outer_smooth s hs a
  · exact Packet06PlacedMaterialGeometry.placed_material_values n hn g η hη.le j s hs a
  · exact Packet06BoundedModalMaterial.placed_bounds _ K
      (Packet06BoundedModalMaterial.rounded_bounds n hn g η hη.le K hK hceil j) s a
end OQ14.Packet06LocalizedVolumeMaterial
#print axioms OQ14.Packet06LocalizedVolumeMaterial.framed_material
