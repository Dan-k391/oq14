import Packet06ExternalPairing
import Packet06ExternalCanonical
import Packet06PhysicalPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalGreen
open Filter Metric MeasureTheory Packet06SectorOperator Packet06MaterialSector
open Packet06ExternalResidue Packet06ExternalCanonical Packet06ExternalPairing
open Packet06RankOneRepair Packet06PhysicalNormalization KernelReciprocity
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

/-- A residue representative: the full free field plus only the selected-sector
scattered correction. Its Laurent residue is physical, but this hybrid is not
asserted to solve the full-source Maxwell equation. -/
def residueRepresentative (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) :
    VectorL2 →L[ℂ] BallL2 T :=
  (z^2)⁻¹ • (localIncident J T z + selectedScattered c S J T z)

theorem selected_residue_representative (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : VectorL2 →L[ℂ] BallL2 T,
      (∀ f, R f =
        (-(∫ x : Maxwell.Space, ∑ i : Fin 3,
          f (VectorFourier.coordinateMap x) i *
            (Packet06LocalPencil.response c z S J u) (VectorFourier.coordinateMap x) i) / (2*z)) •
          ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u)) ∧
      Tendsto (fun v => (v-z) • residueRepresentative c S J T v) (𝓝[≠] z) (𝓝 R) := by
  obtain ⟨R,hR,hlim⟩ := selected_physical_left_residue c ha hm S J T hS hJ hST hc z u w ψ hC hu hψ hd hN
  have hnorm := reciprocalNorm_eq_crossing c S hS z (u : VectorL2)
  rw [hN] at hnorm
  have hcros : vectorPair (deriv (fun v => ComplexConvolutionAnalytic.volumeBlock c v S) z u) u ≠ 0 := by
    intro h
    rw [h,mul_zero] at hnorm
    exact one_ne_zero hnorm
  have hfree : Tendsto (fun v : ℂ => (v-z) • localIncident J T v) (𝓝[≠] z) (𝓝 0) := by
    have hv : Tendsto (fun v : ℂ => v-z) (𝓝[≠] z) (𝓝 0) := by
      simpa only [sub_self] using ((show Continuous (fun v : ℂ => v-z) from continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds))
    have hf := (localIncident_analyticAt J T (by linarith) z).continuousAt.tendsto.mono_left
      (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
    have hh := hv.smul hf
    have hz0 : (0 : ℂ) • localIncident J T z = 0 := by
      ext f
      simp
    rw [hz0] at hh
    exact hh
  have hsum : Tendsto (fun v : ℂ => (v-z) • (localIncident J T v + selectedScattered c S J T v))
      (𝓝[≠] z) (𝓝 R) := by
    simpa only [smul_add,zero_add] using hfree.add hlim
  have hinv : Tendsto (fun v : ℂ => (v^2)⁻¹) (𝓝[≠] z) (𝓝 ((z^2)⁻¹)) :=
    ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hz)).tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨(z^2)⁻¹ • R,?_,?_⟩
  · intro f
    rw [ContinuousLinearMap.smul_apply,hR,incident_physical_pairing c ha hm S J (by linarith) z u f,
      Packet06PhysicalPairing.vectorPair_physical,smul_smul]
    congr 1
    have he : z * vectorPair (deriv (fun v => ComplexConvolutionAnalytic.volumeBlock c v S) z u) u = -2 := by
      linear_combination (2 : ℂ) * hnorm
    have he' : vectorPair (deriv (fun v => ComplexConvolutionAnalytic.volumeBlock c v S) z u) u = -2/z := by
      apply (eq_div_iff hz).2
      linear_combination he
    rw [he']
    field_simp
    ring
  · have h := hinv.smul hsum
    simpa only [residueRepresentative,smul_smul,mul_comm] using h

#print axioms OQ14.Packet06ExternalGreen.selected_residue_representative
end OQ14.Packet06ExternalGreen
