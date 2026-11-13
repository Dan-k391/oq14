import Packet06LocalizedVolumeState
import Packet06PlacedOneSidedCollar

/-! The localized family initializer retains the same actual one-sided collars. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06LocalizedVolumeCollars
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedHost
  Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet06PlacedKernel
  Packet06PhysicalPlacement Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06RigidHotspotState
  Packet06RigidCollar Packet05OneSidedCollar
abbrev Space := Maxwell.Space

theorem initial_collars {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 < η) (j : ℕ)
    (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 z u=1)
    (r B : ℝ) (hrg : r < g.radius)
    (hhot : ∀ i, Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη.le j) z u (body g j) (g.center i) r 0 B)
    (s : ℝ) (hs : 0 < s) (a : Space) (ha : a 2=0)
    (A : Fin N → Set Space) (hA : ∀ i, IsOpen (A i) ∧ A i ⊆ ball (g.center i) g.radius ∧ sphere (g.center i) r ⊆ A i)
    (hcol : ∀ i, OneSidedCollar (rounded n hn g η hη.le j) z u (body g j) (A i) B) :
    HasCollars (Packet06LocalizedVolumeState.initial n hn g η hη j z u hu hN r B hrg hhot s hs a ha)
      (fun i => placement s hs a '' A i) := by
  let h := placement s hs a
  let D : Device N := ⟨n,η,hn,hη,g,j,z,u,s,hs,r,a,scale s*B,fun _ => ∅⟩
  have hc := Packet05RoundedModeSupport.rounded_support n hn g η hη.le j
  have hopen : IsOpen (body g j) := CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hAunit (i : Fin N) : A i ⊆ ball (0 : Space) 1 :=
    (hA i).2.1.trans (ball_subset_closedBall.trans ((closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)))
  have hpos (x : Space) (hx : x ∈ ball (0 : Space) 1) :
      (rounded n hn g η hη.le j).value (VectorFourier.coordinateMap x) ≠ 0 :=
    (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη.le j x hx).ne'
  intro i
  refine ⟨h.isOpenMap _ (hA i).1,?_,?_,?_,?_⟩
  · change h '' A i ⊆ closedBall 0 (1/s+‖a‖)
    exact (Set.image_subset h (hAunit i)).trans (host_enclosed D)
  · intro x hx
    change x ∈ h '' A i at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change (placedCoefficient s a (rounded n hn g η hη.le j)).value (VectorFourier.coordinateMap (h y)) ≠ 0
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb : Packet06CyclicRotation.unrotate (s • (h y-a))=y := h.symm_apply_apply y
    rw [hb]
    exact hpos y (hAunit i hy)
  · intro x hx
    have he : h '' sphere (g.center i) r = sphere (h (g.center i)) (r/s) := by
      ext w
      rw [h.image_eq_preimage]
      change dist (h.symm w) (g.center i)=r ↔ dist w (h (g.center i))=r/s
      have hh := Packet06PlanarProjection.point_distance_pair s hs a (h.symm w) (g.center i)
      change dist (h (h.symm w)) (h (g.center i)) = _ at hh
      rw [h.apply_symm_apply] at hh
      constructor
      · intro ht
        rw [hh,ht,div_eq_mul_inv,mul_comm]
      · intro ht
        rw [hh,div_eq_mul_inv,mul_comm] at ht
        exact (mul_right_cancel₀ (inv_ne_zero hs.ne') ht)
    change x ∈ sphere (h (g.center i)) (r/s) at hx
    rw [← he] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact mem_image_of_mem h ((hA i).2.2 hy)
  · exact Packet06PlacedOneSidedCollar.placed_one_sided_collar _ hc hpos z u hu hN (body g j) (A i)
      hopen (hA i).1 (hAunit i) B (hcol i) s hs a
end OQ14.Packet06LocalizedVolumeCollars
#print axioms OQ14.Packet06LocalizedVolumeCollars.initial_collars
