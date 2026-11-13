import Packet06CertifiedPersistence
import Packet06PoleScale
import Packet06NormalizationLimit

/-! Actual physical unit modes persist with the reusable simple-pole data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06CertifiedNormalization
open Filter Set Metric MeasureTheory Packet06SectorOperator
open StaticCoefficient (Coefficient)
open Packet06SimpleCertificate (Certified)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem physical_certified_modes (c : ℕ → Coefficient) (c₀ : Coefficient) (D S : ℝ)
    (hS : 0 ≤ S) (hb : ∀ j, (c j).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (c j).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (j : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 S → (c j).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : FourierL2.Space, x ∉ closedBall 0 S → c₀.value (VectorFourier.coordinateMap x) = 0)
    (hax : ∀ j, Packet06MaterialSymmetry.Axial (c j))
    (hmer : ∀ j, Packet06MaterialSymmetry.Meridional (c j))
    (hax₀ : Packet06MaterialSymmetry.Axial c₀) (hmer₀ : Packet06MaterialSymmetry.Meridional c₀)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (u₀ : Sector) (hcert : Certified c₀ S z₀ u₀)
    (hN₀ : reciprocalNorm c₀ S z₀ u₀ = 1) :
    ∃ (z : ℕ → ℂ) (v : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ T : ℝ, S ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (c j) (z j) S T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response c₀ z₀ S T u₀))) ∧
      (∀ᶠ j in atTop, z j ≠ 0 ∧ Certified (c j) S (z j) (v j) ∧
        reciprocalNorm (c j) S (z j) (v j) = 1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (c j) (z j) S (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (c j) S (z j) (v j)) := by
  obtain ⟨z,u,hz,hu,hgood⟩ := Packet06CertifiedPersistence.actual_certified_modes
    c c₀ D S hS hb hb₀ ha hc hc₀ hax hmer hax₀ hmer₀ z₀ hz₀ u₀ hcert
  have huV : Tendsto (fun j => (u j : VectorL2)) atTop (𝓝 (u₀ : VectorL2)) :=
    Sector.subtypeL.continuous.tendsto _ |>.comp hu
  have hnorm := Packet06ResponseLimit.reciprocalNorm_tendsto c c₀ D S hS hb hb₀ ha
    z z₀ hz (fun j => (u j : VectorL2)) u₀ huV
  rw [hN₀] at hnorm
  obtain ⟨a,ha',hane,hunit⟩ := Packet06NormalizationLimit.compatible_scales
    (fun j => reciprocalNorm (c j) S (z j) (u j)) 1 1 hnorm one_ne_zero (by norm_num)
  let v : ℕ → Sector := fun j => a j • u j
  have hv : Tendsto v atTop (𝓝 u₀) := by simpa only [one_smul] using ha'.smul hu
  have hvV : Tendsto (fun j => (v j : VectorL2)) atTop (𝓝 (u₀ : VectorL2)) :=
    Sector.subtypeL.continuous.tendsto _ |>.comp hv
  refine ⟨z,v,hz,hv,?_,?_⟩
  · intro T hT
    exact Packet06ResponseLimit.response_tendsto c c₀ D S T (by linarith) hb hb₀ ha
      z z₀ hz (fun j => (v j : VectorL2)) u₀ hvV
  · filter_upwards [hgood,hunit] with j hj hNj
    have hcv : Certified (c j) S (z j) (v j) :=
      Packet06SimpleCertificate.certified_scale (c j) S (z j) (u j) hj.2.1 (a j) (hane j)
    have hne : (v j : VectorL2) ≠ 0 := fun h =>
      Packet06SimpleCertificate.certified_nonzero (c j) S (z j) (v j) hcv (Subtype.ext h)
    have hk := hcv.choose_spec.choose_spec.2.1
    refine ⟨hj.1,hcv,?_,Packet06OutgoingMode.actual_outgoing_mode
      (c j) (z j) S hS (v j) (hc j) hk hne,?_⟩
    · change reciprocalNorm (c j) S (z j) (a j • (u j : VectorL2)) = 1
      rw [Packet06PhysicalScale.reciprocalNorm_scale _ S hS]
      exact hNj
    · exact Packet06PoleScale.observed_pole_scale (c j) S (z j) (u j) (a j) (hane j) hj.2.2

end OQ14.Packet06CertifiedNormalization
#print axioms OQ14.Packet06CertifiedNormalization.physical_certified_modes
