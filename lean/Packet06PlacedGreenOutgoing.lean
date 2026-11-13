import Packet06PlacedGreenSource
import Packet06CyclicOutgoing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedGreenOutgoing
open MeasureTheory Metric Filter Maxwell Packet06CyclicRotation Packet06CyclicRotationMaxwell
open Packet06PlacedEquivalence Packet06PlacedGreenSource Packet06CyclicOutgoing
open scoped Topology
abbrev V := VectorFourier.VectorL2

/-- The actual placed projected-source field has a complex outgoing far limit
on rays based at the device's translated center. -/
theorem centered_outgoing (c : StaticCoefficient.Coefficient) (S J : ℝ)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) (z : ℂ) (f : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (s : ℝ) (hs : 0 < s) (a n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor ((s : ℂ)*z) r *
      ((((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) *
        rotateField (Packet06ProjectedGlobal.field c S J z ((placed s hs a).symm f))
          (s • ((a+r • n)-a)) i)) atTop
      (𝓝 ((((s : ℂ)^3)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) *
        ((z^2)⁻¹ * (ComplexDyadicOutgoing.amplitude (Packet06ExternalFreeMaxwell.supportCoefficient J) z
          (Packet06ProjectedGreen.project ((placed s hs a).symm f)) (unrotate n) (WeakCurl.previous i) +
        ComplexDyadicOutgoing.amplitude c z (Ring.inverse (Packet06MaterialSector.pencil c S z)
          (Packet06ExternalResidue.incidentDatum c S J z
            (Packet06ProjectedGreen.project ((placed s hs a).symm f)))) (unrotate n) (WeakCurl.previous i))))) := by
  let F := Packet06ProjectedGlobal.field c S J z ((placed s hs a).symm f)
  let A : Space → Vector := fun v j => (z^2)⁻¹ *
    (ComplexDyadicOutgoing.amplitude (Packet06ExternalFreeMaxwell.supportCoefficient J) z
       (Packet06ProjectedGreen.project ((placed s hs a).symm f)) v j +
     ComplexDyadicOutgoing.amplitude c z (Ring.inverse (Packet06MaterialSector.pencil c S z)
       (Packet06ExternalResidue.incidentDatum c S J z
         (Packet06ProjectedGreen.project ((placed s hs a).symm f)))) v j)
  have hF : ∀ v : Space, ‖v‖ = 1 → ∀ j : Fin 3,
      Tendsto (fun r : ℝ => factor z r * F (r • v) j) atTop (𝓝 (A v j)) := by
    intro v hv j
    exact Packet06ProjectedGlobal.field_outgoing c S J hS hJ z _ hc v hv j
  have h := (tendsto_const_nhds.mul
    (rotated_scaled_centered_limit F A z s hs a n hn hF i) :
      Tendsto (fun r : ℝ => (((s : ℂ)^3)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) *
        (factor ((s : ℂ)*z) r * ((s : ℂ) * rotateField F (s • ((a+r • n)-a)) i)))
        atTop _)
  apply h.congr'
  filter_upwards with r
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  dsimp only [F]
  field_simp
  ring

#print axioms OQ14.Packet06PlacedGreenOutgoing.centered_outgoing
end OQ14.Packet06PlacedGreenOutgoing
