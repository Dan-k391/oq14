import Packet06RigidWeightedMaximum
import Packet06AxialHotspotGeometry

/-! Actual material-side weighted maxima are carried by axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AxialWeightedMaximum
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PhaseWeightedMaximum Packet06AxialMaterialTransport Packet06AxialPhaseField Packet06RigidWeightedMaximum
abbrev Space := Maxwell.Space

 theorem axial_weighted (θ : ℝ) (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (body K : Set Space) (hb : IsOpen body) (hK : MeasurableSet K) (hKT : K ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ K, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hmax : HasWeightedMaximum c z u body K n η inside outside b x) :
    HasWeightedMaximum (coefficient θ c) z (action θ u) ((rotation θ) '' body) ((rotation θ) '' K) n η
      (transport θ inside) (transport θ outside) b (rotation θ x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b) (rotation θ x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  obtain ⟨hi,ho,hiae,hoae,hx,hmax⟩ := hmax
  have ht := Packet06AxialTraceCollar.rotated_trace_collar_general θ c R T hR hRT hc z u hu hN body K ∅
    hb hK hKT hpos inside outside hi ho hiae hoae 0 (by intro p y hy; exact False.elim hy.1)
  obtain ⟨hci,hco,heai,heao,_⟩ := ht
  have hx' : rotation θ x ∈ (rotation θ) '' K ∩ phaseDomain ((rotation θ) '' body) b := by
    refine ⟨mem_image_of_mem _ hx.1,?_⟩
    rw [← Packet06AxialHotspotGeometry.image_phase θ body b]
    exact mem_image_of_mem _ hx.2
  have hv : ∀ b' y, y ∈ (rotation θ) '' K ∩ phaseDomain ((rotation θ) '' body) b' →
      phasePermittivity n η b' * (physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b') y)^2 ≤
        phasePermittivity n η b * (physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b) (rotation θ x))^2 := by
    intro b' y hy
    obtain ⟨q,hq,rfl⟩ := hy.1
    have hq' : q ∈ phaseDomain body b' := by
      rw [← Packet06AxialHotspotGeometry.image_phase θ body b'] at hy
      exact (rotation θ).injective.mem_set_image.mp hy.2
    simpa [phase_transport,amplitude_transport,rotation,spatial_inverse] using hmax b' q ⟨hq,hq'⟩
  refine ⟨⟨hci,hco,heai,heao,hx',hv⟩,?_⟩
  simp [phase_transport,amplitude_transport,rotation,spatial_inverse]
end OQ14.Packet06AxialWeightedMaximum
#print axioms OQ14.Packet06AxialWeightedMaximum.axial_weighted
