import Packet06ProjectedGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedModePairing
open MeasureTheory Metric Set Maxwell Packet06SectorOperator Packet06LocalPencil
open Packet06ProjectedGreen Packet06ProjectedSupport Packet06ExternalSymmetry
open Packet06ExternalOverlap Packet06ExternalFreeMaxwell KernelReciprocity Packet06SectorConjugate
abbrev VectorL2 := VectorFourier.VectorL2

theorem material_source_supported (c : StaticCoefficient.Coefficient) (S : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorL2) :
    ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 S →
      StaticCoefficient.sqrtMultiplier c u (VectorFourier.coordinateMap x) = 0 := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c u)
  filter_upwards [h] with x hx hout
  rw [hx,hc x hout]
  simp

/-- The selected projector may be removed from a compact source in the physical
mode coupling; the actual local mode representative is used on the source ball. -/
theorem source_projection_pair (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hS : 0 ≤ S)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : Sector) (f : VectorL2)
    (hf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    vectorPair (project f) (response c z S J u) = vectorPair f (response c z S J u) := by
  let R := max S J
  let b := supportCoefficient R
  let a := supportCoefficient J
  let v := StaticCoefficient.sqrtMultiplier c u
  let U := 2*R-S
  have hSR : S ≤ R := le_max_left _ _
  have hJR : J ≤ R := le_max_right _ _
  have hR : 0 ≤ R := hS.trans hSR
  have hJU : J ≤ U := by dsimp [U]; linarith
  have hvS := material_source_supported c S hc u
  have hvR : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 R → v (VectorFourier.coordinateMap x) = 0 := by
    filter_upwards [hvS] with x hx hout
    exact hx (fun hin => hout (closedBall_subset_closedBall hSR hin))
  have hfixed : StaticCoefficient.sqrtMultiplier b v = v := supported_multiplier_identity R v hvR
  have hv : v ∈ Sector := sqrt_mem_sector c ha hm u u.property
  have hvol : ComplexConvolutionAnalytic.volumeBlock b z R v ∈ Sector :=
    volume_mem_sector b (supportCoefficient_axial R) (supportCoefficient_meridional R) R hR
      (supportCoefficient_support R) z v hv
  let E : VectorL2 := StaticCoefficient.sqrtMultiplier b (kernel z R R v)
  have hE : E ∈ Sector := by
    have he := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A v) (weighted_block_eq b z R)
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply,hfixed] at he
    have he' : E = v - ComplexConvolutionAnalytic.volumeBlock b z R v := by
      dsimp [E]
      rw [he]
      abel
    rw [he']
    exact Sector.sub_mem hv hvol
  have hcut : StaticCoefficient.sqrtMultiplier a (kernel z R R v) =
      StaticCoefficient.sqrtMultiplier a (kernel z S J v) := by
    have h := weighted_free_overlap a z S J U hJU v (supportCoefficient_support J) hvS
    have hkernel : kernel z S U = kernel z R R := by
      unfold kernel
      have hh : U+S = R+R := by dsimp [U]; ring
      rw [hh]
    rw [hkernel] at h
    exact h
  have hpf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → (project f) (VectorFourier.coordinateMap x) = 0 :=
    projected_supported J f hf
  have haf : StaticCoefficient.sqrtMultiplier a f = f := supported_multiplier_identity J f hf
  have hapf : StaticCoefficient.sqrtMultiplier a (project f) = project f := supported_multiplier_identity J (project f) hpf
  have hfR : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 R → f (VectorFourier.coordinateMap x) = 0 := by
    filter_upwards [hf] with x hx hout
    exact hx (fun hin => hout (closedBall_subset_closedBall hJR hin))
  have hpfR : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 R → (project f) (VectorFourier.coordinateMap x) = 0 := by
    filter_upwards [hpf] with x hx hout
    exact hx (fun hin => hout (closedBall_subset_closedBall hJR hin))
  have hbf : StaticCoefficient.sqrtMultiplier b f = f := supported_multiplier_identity R f hfR
  have hbpf : StaticCoefficient.sqrtMultiplier b (project f) = project f := supported_multiplier_identity R (project f) hpfR
  have hlocal (q : VectorL2) (haq : StaticCoefficient.sqrtMultiplier a q = q)
      (hbq : StaticCoefficient.sqrtMultiplier b q = q) :
      vectorPair q E = vectorPair q (response c z S J u) := by
    dsimp only [E]
    rw [← NewtonReciprocity.sqrtMultiplier_reciprocity, hbq]
    rw [← haq, NewtonReciprocity.sqrtMultiplier_reciprocity, hcut,
      ← NewtonReciprocity.sqrtMultiplier_reciprocity, haq]
    rfl
  rw [← hlocal (project f) hapf hbpf, ← hlocal f haf hbf]
  exact projection_pair_right f E hE

#print axioms OQ14.Packet06ProjectedModePairing.material_source_supported
#print axioms OQ14.Packet06ProjectedModePairing.source_projection_pair
end OQ14.Packet06ProjectedModePairing
