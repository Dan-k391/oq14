import Packet06RigidInitial
import Packet06LocalizedVolumeFamily

/-! A single actual localized rounded mode provides the rigid-frame State,
with the literal placed material, field, body, centers and scaled radius. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06LocalizedVolumeState
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedHost
  Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet06PlacedKernel
  Packet06PhysicalPlacement Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06RigidHotspotState
abbrev Space := Maxwell.Space

def initial {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 < η) (j : ℕ)
    (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 z u=1)
    (r B : ℝ) (hrg : r < g.radius)
    (hhot : ∀ i, Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη.le j) z u (body g j) (g.center i) r 0 B)
    (s : ℝ) (hs : 0 < s) (a : Space) (ha : a 2=0) :
    State N ((s : ℂ)*z) (r/s) 0 (scale s*B) := by
  let c := rounded n hn g η hη.le j
  let h := placement s hs a
  let D : Device N := ⟨n,η,hn,hη,g,j,z,u,s,hs,r,a,scale s*B,fun _ => ∅⟩
  have hc := Packet05RoundedModeSupport.rounded_support n hn g η hη.le j
  have hball (i : Fin N) : closedBall (g.center i) r ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall (hrg.le.trans g.radius_outer)).trans (g.outer_inside i)
  have hplaced := placed_normalized_kernel c 1 (by norm_num) hc z u hu hN s hs a
  have hopen : IsOpen (body g j) := CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hobs (i : Fin N) : closedBall (h (g.center i)) (r/s) ⊆ h '' ball (0 : Space) 1 := by
    rw [← image_closedBall]
    exact Set.image_subset _ (hball i)
  have henclose : h '' ball (0 : Space) 1 ⊆ closedBall (0 : Space) (1/s+‖a‖) := by
    exact host_enclosed D
  refine ⟨placedCoefficient s a c,placedUnknown s a u,1/s+‖a‖,
    add_nonneg (div_nonneg (by norm_num) hs.le) (norm_nonneg a),hplaced.1,hplaced.2.1,hplaced.2.2.1,
    h '' body g j,{x : Space | x 2=0},fun i => h (g.center i),h.isOpenMap _ hopen,?_,?_,?_⟩
  · intro i
    exact (hobs i).trans henclose
  · intro i x hx
    obtain ⟨y,hy,rfl⟩ := hobs i hx
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb := h.symm_apply_apply y
    have hb' : Packet06CyclicRotation.unrotate (s • (h y-a))=y := hb
    rw [hb']
    exact (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη.le j y hy).ne'
  · intro i
    have hh := Packet06PlacedHotspot.placed_actual_hotspot c hc
      (fun x hx => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη.le j x hx).ne')
      z u hu hN (body g j) hopen (g.center i) r 0 B (hball i) (hhot i) s hs a ha
    have hh' : Packet06PlacedHotspot.PhysicalHotspot (placedCoefficient s a c) ((s : ℂ)*z)
        (placedUnknown s a u) (h '' body g j) (h (g.center i)) (r/s) 0 (scale s*B) := by
      simpa only [mul_zero] using hh
    exact Packet06AxialHotspotStart.coordinate_hotspot _ _ _ _ _ _ _ _ hh'

end OQ14.Packet06LocalizedVolumeState
#print axioms OQ14.Packet06LocalizedVolumeState.initial
