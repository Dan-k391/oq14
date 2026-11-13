import Packet06RoundedInsertion

/-! Actual rounded fixed-contrast devices carry physical unit high-Q modes
converging to the same selected sharp-device mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06RoundedMode
open Filter Set Metric MeasureTheory Packet06MaterialSymmetry Packet06RoundedInsertion
open Packet06SectorOperator Packet06SimpleCertificate
open StaticCoefficient (Coefficient)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology
variable {ι : Type*} [Fintype ι]

theorem normalized_rounded_modes (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ)
    (center : ι → Maxwell.Space) (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j))
    (ha0 : ∀ i, 0 < a i) (base : Coefficient) (η : ℝ) (hη : 0 ≤ η)
    (hbase : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 → base.value (VectorFourier.coordinateMap x) = 0)
    (hax : Axial base) (hmer : Meridional base)
    (haxis : Packet06ConeUnionSymmetry.OnAxis center)
    (hinside : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Maxwell.Space) 1)
    (z₀ : ℂ) (u₀ : Sector)
    (hcert : Certified (sharp p a center B hB hcontrast ha hsep base η hη) 1 z₀ u₀)
    (hN : reciprocalNorm (sharp p a center B hB hcontrast ha hsep base η hη) 1 z₀ u₀ = 1)
    (hre : 0 < z₀.re) (him : z₀.im < 0) (Q : ℝ) (hQ : Q < z₀.re / (-2*z₀.im)) :
    let c := rounded p a center B hB hcontrast ha hsep ha0 base η hη
    let c₀ := sharp p a center B hB hcontrast ha hsep base η hη
    ∃ (z : ℕ → ℂ) (v : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (c j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response c₀ z₀ 1 T u₀))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re / (-2*(z j).im) ∧
        Certified (c j) 1 (z j) (v j) ∧ reciprocalNorm (c j) 1 (z j) (v j) = 1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (c j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (c j) 1 (z j) (v j)) := by
  dsimp only
  have hz₀ : z₀ ≠ 0 := by intro h; simp only [h,Complex.zero_re] at hre; exact lt_irrefl _ hre
  obtain ⟨hb,hb₀,hconv,hc,hc₀,haxc,hmerc,hax₀,hmer₀⟩ :=
    admissible p a center B hB hcontrast ha hsep ha0 base η hη hbase hax hmer haxis hinside
  obtain ⟨z,v,hz,hv,hresponse,hgood⟩ := Packet06CertifiedNormalization.physical_certified_modes
    (rounded p a center B hB hcontrast ha hsep ha0 base η hη)
    (sharp p a center B hB hcontrast ha hsep base η hη)
    (base.bound+η*B) 1 (by norm_num) hb hb₀ hconv hc hc₀ haxc hmerc hax₀ hmer₀ z₀ hz₀ u₀ hcert hN
  have hqual := Packet06HighQualityBranch.quality_stable z z₀ hz Q hre him hQ
  refine ⟨z,v,hz,hv,hresponse,?_⟩
  filter_upwards [hgood,hqual] with j hj hQj
  exact ⟨hQj.1,hQj.2.1,hQj.2.2,hj.2⟩

end OQ14.Packet06RoundedMode
#print axioms OQ14.Packet06RoundedMode.normalized_rounded_modes
