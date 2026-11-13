import Packet06RigidWeightedStep

/-! A weighted maximum and its *same* branches on a larger neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06NeighborhoodWeighted
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet06RigidHotspotState Packet06RigidWeightedMaximum
  Packet06PhaseWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum
abbrev Space := Maxwell.Space

def Trace (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (body K : Set Space) (inside outside : Fin 3 → Space → ℂ) : Prop :=
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
  (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
  (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
  (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
  (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i)

def Certificate {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) (i : Fin N)
    (K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space) : Prop :=
  MeasurableSet K ∧ K ⊆ closedBall 0 d.supportRadius ∧
  (∀ y ∈ K, d.material.value (VectorFourier.coordinateMap y) ≠ 0) ∧
  closedBall (d.center i) r ⊆ K ∧
  Trace d.material z d.unknown d.body K inside outside ∧
  HasWeightedMaximum d.material z d.unknown d.body (closedBall (d.center i) r) n η inside outside b x

theorem axial {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B)
    (i : Fin N) (K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (h : Certificate d i K n η inside outside b x) :
    Certificate (axial θ d) i ((rotation θ) '' K) n η
      (Packet06AxialPhaseField.transport θ inside) (Packet06AxialPhaseField.transport θ outside) b (rotation θ x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (Packet06AxialPhaseField.transport θ inside)
      (Packet06AxialPhaseField.transport θ outside) b) (rotation θ x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  obtain ⟨hK,hKT,hpos,hsub,⟨hi,ho,hiae,hoae⟩,hmax⟩ := h
  have hm := Packet06RigidWeightedStep.axial_step θ d i n η inside outside b x hmax
  have ht := Packet06AxialTraceCollar.rotated_trace_collar_general θ d.material d.supportRadius d.supportRadius
    d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization d.body K ∅
    d.body_open hK hKT hpos inside outside hi ho hiae hoae 0 (by intro p y hy; exact False.elim hy.1)
  let e := (rotation θ).toHomeomorph
  refine ⟨⟨?_,?_,?_,?_,⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩,hm.1⟩,hm.2⟩
  · change MeasurableSet (e '' K)
    rw [e.image_eq_preimage]
    exact hK.preimage e.symm.continuous.measurable
  · rintro y ⟨q,hq,rfl⟩
    simpa [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using hKT hq
  · rintro y ⟨q,hq,rfl⟩
    change (Packet06AxialMaterialTransport.coefficient θ d.material).value (VectorFourier.coordinateMap (rotation θ q)) ≠ 0
    rw [Packet06AxialMaterialTransport.coefficient_value]
    simpa [rotation,spatial_inverse] using hpos q hq
  · change closedBall (rotation θ (d.center i)) r ⊆ (rotation θ) '' K
    rw [←Packet06AxialHotspotGeometry.image_closedBall θ (d.center i) r]
    exact image_subset _ hsub
end OQ14.Packet06NeighborhoodWeighted
#print axioms OQ14.Packet06NeighborhoodWeighted.axial
