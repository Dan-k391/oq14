import Packet06ExternalSymmetry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedSupport
open MeasureTheory Metric Set Maxwell Packet06SectorOperator Packet06ExternalFreeMaxwell Packet06ExternalSymmetry
open scoped InnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem symmetric_multiplier_projection (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (f : VectorL2) :
    (Sector.orthogonalProjection (StaticCoefficient.sqrtMultiplier c f) : VectorL2) =
      StaticCoefficient.sqrtMultiplier c (Sector.orthogonalProjection f : VectorL2) := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · exact sqrt_mem_sector c ha hm _ (Sector.orthogonalProjection f).property
  · intro w hw
    rw [← map_sub, StaticCoefficient.sqrtMultiplier_symmetric]
    exact Submodule.orthogonalProjection_inner_eq_zero f _ (sqrt_mem_sector c ha hm w hw)

theorem projected_supported (J : ℝ) (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J →
      (Sector.orthogonalProjection f : VectorL2) (VectorFourier.coordinateMap x) = 0 := by
  let b := supportCoefficient J
  let g : VectorL2 := Sector.orthogonalProjection f
  have hfixed : StaticCoefficient.sqrtMultiplier b g = g := by
    rw [← symmetric_multiplier_projection b (supportCoefficient_axial J) (supportCoefficient_meridional J) f,
      supported_multiplier_identity J f hf]
  have hmul := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae b g)
  filter_upwards [hmul] with x hx hnot
  rw [hfixed] at hx
  change g (VectorFourier.coordinateMap x) =
    (Real.sqrt (b.value (VectorFourier.coordinateMap x)) : ℂ) • g (VectorFourier.coordinateMap x) at hx
  rw [supportCoefficient_support J x hnot] at hx
  simpa using hx

#print axioms OQ14.Packet06ProjectedSupport.symmetric_multiplier_projection
#print axioms OQ14.Packet06ProjectedSupport.projected_supported
end OQ14.Packet06ProjectedSupport
