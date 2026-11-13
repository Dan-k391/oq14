import Packet06NeighborhoodWeighted

/-! Translation-plus-cyclic and cyclic transport preserve larger-neighborhood certificates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06NeighborhoodWeightedAffine
open MeasureTheory Set Metric Maxwell Packet06RigidHotspotState Packet06RigidWeightedMaximum
  Packet06NeighborhoodWeighted Packet06PhaseWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedKernel
abbrev Space := Maxwell.Space

theorem affine {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B)
    (i : Fin N) (K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hc : Certificate d i K n η inside outside b x) :
    let h := placement 1 (by norm_num) a
    Certificate (affine a d) i (h '' K) n η (transport 1 (by norm_num) a inside)
      (transport 1 (by norm_num) a outside) b (h x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (transport 1 (by norm_num) a inside)
      (transport 1 (by norm_num) a outside) b) (h x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  dsimp only
  obtain ⟨hK,hKT,hpos,hsub,⟨hi,ho,hiae,hoae⟩,hmax⟩ := hc
  have hm := Packet06RigidWeightedStep.affine_step a d i n η inside outside b x hmax
  have ht := Packet06AffineTraceGeneral.affine_trace_general d.material d.supportRadius d.supportRadius
    d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization a d.body K ∅
    d.body_open hK hKT hpos inside outside hi ho hiae hoae 0 (by intro p y hy; exact False.elim hy.1)
  let h := placement 1 (by norm_num) a
  refine ⟨⟨?_,?_,?_,?_,⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩,hm.1⟩,hm.2⟩
  · change MeasurableSet (h '' K)
    rw [h.image_eq_preimage]
    exact hK.preimage h.symm.continuous.measurable
  · rintro y ⟨q,hq,rfl⟩
    have hq' : ‖q‖ ≤ d.supportRadius := by simpa [mem_closedBall,dist_zero_right] using hKT hq
    have hp : h q = a + Packet06CyclicRotation.rotate q := by
      change Packet06PhysicalPlacement.point 1 a q = _
      simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
    have hh := norm_add_le a (Packet06CyclicRotation.rotate q)
    rw [Packet06CyclicRotation.rotate_norm] at hh
    change h q ∈ closedBall 0 (d.supportRadius+‖a‖)
    rw [mem_closedBall,dist_zero_right,hp]
    linarith
  · rintro y ⟨q,hq,rfl⟩
    change (placedCoefficient 1 a d.material).value (VectorFourier.coordinateMap (h q)) ≠ 0
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb : Packet06CyclicRotation.unrotate ((1 : ℝ) • (h q-a))=q := by
      have hp : h q = a + Packet06CyclicRotation.rotate q := by
        change Packet06PhysicalPlacement.point 1 a q = _
        simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
      rw [hp]
      simp only [add_sub_cancel_left,one_smul,Packet06CyclicRotation.unrotate_rotate]
    exact fun hz => hpos q hq ((congrArg (fun y => d.material.value (VectorFourier.coordinateMap y)) hb).symm.trans hz)
  · change closedBall (h (d.center i)) r ⊆ h '' K
    have hball := image_closedBall 1 (by norm_num) a (d.center i) r
    simp only [div_one] at hball
    rw [←hball]
    exact image_subset _ hsub

theorem cyclic {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B)
    (i : Fin N) (K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hc : Certificate d i K n η inside outside b x) :
    let h := placement 1 (by norm_num) 0
    Certificate (cyclic d) i (h '' K) n η (transport 1 (by norm_num) 0 inside)
      (transport 1 (by norm_num) 0 outside) b (h x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (transport 1 (by norm_num) 0 inside)
      (transport 1 (by norm_num) 0 outside) b) (h x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  have h := affine 0 d i K n η inside outside b x hc
  simpa only [Packet06RigidHotspotState.affine,Packet06RigidHotspotState.cyclic,norm_zero,add_zero] using h
end OQ14.Packet06NeighborhoodWeightedAffine
#print axioms OQ14.Packet06NeighborhoodWeightedAffine.affine
#print axioms OQ14.Packet06NeighborhoodWeightedAffine.cyclic
