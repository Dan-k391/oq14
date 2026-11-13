import Packet06RigidWeightedMaximum
import Packet06PlacementHomeomorph

/-! Actual material-side weighted maxima are carried by cyclic rotation
and arbitrary translation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AffineWeightedMaximum
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PhaseWeightedMaximum Packet06PlacedKernel Packet06PlacedPhaseField Packet06PlacementHomeomorph
  Packet06RigidWeightedMaximum
abbrev Space := Maxwell.Space

theorem affine_weighted (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (a : Space)
    (body K : Set Space) (hb : IsOpen body) (hK : MeasurableSet K) (hKT : K ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ K, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hmax : HasWeightedMaximum c z u body K n η inside outside b x) :
    let h := placement 1 (by norm_num) a
    HasWeightedMaximum (placedCoefficient 1 a c) z (placedUnknown 1 a u) (h '' body) (h '' K) n η
      (transport 1 (by norm_num) a inside) (transport 1 (by norm_num) a outside) b (h x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (transport 1 (by norm_num) a inside)
      (transport 1 (by norm_num) a outside) b) (h x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  dsimp only
  let h := placement 1 (by norm_num) a
  obtain ⟨hi,ho,hiae,hoae,hx,hmax⟩ := hmax
  have ht := Packet06AffineTraceGeneral.affine_trace_general c R T hR hRT hc z u hu hN a body K ∅
    hb hK hKT hpos inside outside hi ho hiae hoae 0 (by intro p y hy; exact False.elim hy.1)
  obtain ⟨hci,hco,heai,heao,_⟩ := ht
  have hx' : h x ∈ h '' K ∩ phaseDomain (h '' body) b := by
    refine ⟨mem_image_of_mem _ hx.1,?_⟩
    rw [← image_phase 1 (by norm_num) a body b]
    exact mem_image_of_mem _ hx.2
  have hv : ∀ b' y, y ∈ h '' K ∩ phaseDomain (h '' body) b' →
      phasePermittivity n η b' * (physicalAmplitude (phaseField (transport 1 (by norm_num) a inside)
        (transport 1 (by norm_num) a outside) b') y)^2 ≤
      phasePermittivity n η b * (physicalAmplitude (phaseField (transport 1 (by norm_num) a inside)
        (transport 1 (by norm_num) a outside) b) (h x))^2 := by
    intro b' y hy
    have hyK : h.symm y ∈ K := by
      rcases hy.1 with ⟨q,hq,rfl⟩
      simpa [h] using hq
    have hyP : h.symm y ∈ phaseDomain body b' := by
      have hh := hy.2
      rw [← image_phase 1 (by norm_num) a body b', h.image_eq_preimage] at hh
      exact hh
    rw [phase_transport,amplitude_transport,phase_transport,amplitude_transport,h.symm_apply_apply]
    simpa [scale] using hmax b' (h.symm y) ⟨hyK,hyP⟩
  refine ⟨⟨hci,hco,heai,heao,hx',hv⟩,?_⟩
  rw [phase_transport,amplitude_transport,h.symm_apply_apply]
  simp [scale]
end OQ14.Packet06AffineWeightedMaximum
#print axioms OQ14.Packet06AffineWeightedMaximum.affine_weighted
