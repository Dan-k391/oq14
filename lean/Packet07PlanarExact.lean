import Packet07PlanarSetup
import Packet07BinaryExact

/-! Constructed finite planar binary peak packing at sufficiently small frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.Packet07PlanarExact
open Filter MeasureTheory Set Metric Packet07PlanarSetup
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

/-- For every positive finite N and open planar patch, construct the geometry,
    common positive binary contrast, one normalized finite harmonic input, and one
    rounded actual device with simultaneous prescribed essential peak thresholds.
    The material is the union of 2N open, nonempty, pairwise disjoint lobes. -/
theorem planar_binary_peaks_small_frequency (N : ℕ) (hN : 0 < N)
    (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ g : Setup N P d t, ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ →
      ∃ input : Input, input ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k input) atTop (𝓝 1) ∧
      ∀ thresholds : Fin N → ℝ, ∃ (n : ℕ) (components : Fin N → Fin 3),
        MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (g.rounded n))
          (g.electric k n input) (g.magnetic k n input) ∧
        (∀ i, 0 < (volume.restrict (ball (g.centers i) (g.radius/2)))
          {x | thresholds i < ‖g.electric k n input x (components i)‖}) ∧
        IsOpen (CommonBinaryInterface.body g.dataFamily g.radii g.centers n) ∧
        CommonBinaryInterface.body g.dataFamily g.radii g.centers n ⊆ closedBall (0 : Space) g.enclosing ∧
        (∀ i : Fin N, ∀ up : Bool, (Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i up).Nonempty) ∧
        (∀ i j : Fin N × Bool, i ≠ j → Disjoint
          (Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2)
          (Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n j.1 j.2)) ∧
        (∀ x : Space, x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers n ↔
          ∃ i : Fin N, ∃ up : Bool, x ∈ Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i up) ∧
        (∀ i : Fin N × Bool, ∀ x ∈ Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2,
          connectedComponentIn (CommonBinaryInterface.body g.dataFamily g.radii g.centers n) x =
            Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2) ∧
        (∀ x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers n,
          ∃! i : Fin N × Bool, connectedComponentIn (CommonBinaryInterface.body g.dataFamily g.radii g.centers n) x =
            Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2) ∧
        (∀ x ∈ frontier (CommonBinaryInterface.body g.dataFamily g.radii g.centers n),
          ∃ f : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
            ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers n ↔ 0 < f y)) ∧
        (∀ x : Space, (g.rounded n).value (VectorFourier.coordinateMap x) =
          (by classical exact if x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers n then d else 0)) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨g⟩ := Packet07PlanarSetup.exists_setup N P hP hne d t hd ht ht1
  have hb0 : ∀ i : Fin N, 0 < g.radius/2 := fun _ => half_pos g.radius_pos
  have hb : ∀ i : Fin N, g.radius/2 < g.radii i := fun _ => by dsimp [Setup.radii]; linarith [g.radius_pos]
  have hν : ∀ i : Fin N, (g.dataFamily i).exponent < 1 := fun _ => g.exponent_lt_one
  have hra : ∀ i : Fin N, 0 ≤ g.radii i := fun _ => g.radius_pos.le
  have hgeom : ∀ i j : Fin N, i ≠ j → g.radii i + g.radii j < dist (g.centers i) (g.centers j) := g.separation
  have hR : ∀ i : Fin N, ConicalCommonMaterial.outer g.dataFamily g.centers i ⊆ closedBall (0 : Space) g.enclosing := g.outer_enclosed
  have hai : ∀ i : Fin N, g.radii i < (g.dataFamily i).cutoff.rIn := fun _ => g.radius_in
  have hcommon : ∀ i : Fin N, (g.dataFamily i).contrast = d := fun _ => g.contrast_eq
  obtain ⟨δ,hδ,hex⟩ := Packet07BinaryExact.one_smooth_binary_lobes g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.enclosing
    (fun _ => g.radius/2) d hcommon g.enclosing_nonnegative le_rfl hb0 hb hν hra hgeom g.balls_enclosed hR hai
  refine ⟨g,δ,hδ,?_⟩
  intro k hk hkd
  obtain ⟨input,hin,hpower,hpeak⟩ := hex k hk hkd
  refine ⟨input,hin,hpower,?_⟩
  intro thresholds
  obtain ⟨n,components,hm,hpeak,hopen,hsupport,hcomponent,hnonempty,hdisjoint,hcover,hexact,hunique,hsmooth,hvalue⟩ :=
    hpeak (fun _ => g.radius/2) hb0 (fun _ => le_rfl) thresholds
  exact ⟨n,components,hm,hpeak,hopen,hsupport,hnonempty,hdisjoint,hcover,hexact,hunique,hsmooth,hvalue⟩

end OQ14.Packet07PlanarExact
#print axioms OQ14.Packet07PlanarExact.planar_binary_peaks_small_frequency
