import Packet06PlacedGreenFarShift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06PlacedGreenOriginOutgoing
open Complex MeasureTheory Metric Filter Maxwell Packet06CyclicRotation Packet06CyclicRotationMaxwell
open Packet06PlacedEquivalence Packet06PlacedGreenFarShift Packet06CyclicOutgoing
open scoped Topology
abbrev V := VectorFourier.VectorL2

/-- Ordinary origin-centered outgoing limit of the actual placed Green field. -/
theorem origin_outgoing (c : StaticCoefficient.Coefficient) (S J : ℝ)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) (z : ℂ) (f : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (s : ℝ) (hs : 0 < s) (a n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor ((s : ℂ)*z) r *
      ((((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) *
        rotateField (Packet06ProjectedGlobal.field c S J z ((placed s hs a).symm f))
          (s • (r • n-a)) i)) atTop
      (𝓝 ((((s : ℂ)^3)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) *
        ((z^2)⁻¹ * (shiftedAmplitude (Packet06ExternalFreeMaxwell.supportCoefficient J) z
          (Packet06ProjectedGreen.project ((placed s hs a).symm f)) (unrotate n) (s • unrotate a) (WeakCurl.previous i) +
        shiftedAmplitude c z (Ring.inverse (Packet06MaterialSector.pencil c S z)
          (Packet06ExternalResidue.incidentDatum c S J z
            (Packet06ProjectedGreen.project ((placed s hs a).symm f)))) (unrotate n) (s • unrotate a) (WeakCurl.previous i))))) := by
  have hu : ‖unrotate n‖ = 1 := by
    have h := rotation.symm.norm_map n
    change ‖unrotate n‖ = ‖n‖ at h
    rw [h,hn]
  have hf := (projected_shifted_limit c S J hS hJ z ((placed s hs a).symm f) hc
    (unrotate n) (s • unrotate a) hu (WeakCurl.previous i)).comp (tendsto_id.const_mul_atTop hs)
  have hh := hf.const_mul (((s : ℂ)^3)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ))
  apply hh.congr'
  filter_upwards with r
  have hrot : unrotate (s • (r • n-a)) = (s*r) • unrotate n - s • unrotate a := by
    change rotation.symm (s • (r • n-a)) = _
    simp only [map_smul,map_sub,smul_sub,smul_smul]
    rfl
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  dsimp only [rotateField]
  rw [hrot]
  have hfactor := factor_scale s r z
  unfold factor at hfactor ⊢
  push_cast at hfactor
  simp only [Function.comp_apply,id_eq,Complex.ofReal_mul]
  rw [← hfactor]
  field_simp
  ring

#print axioms OQ14.Packet06PlacedGreenOriginOutgoing.origin_outgoing
end OQ14.Packet06PlacedGreenOriginOutgoing
