import Packet06PlacedGreenObservation
import Packet06PlacedGreenPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PlacedGreenResidue
open Filter MeasureTheory Metric Maxwell Packet06PlacedEquivalence Packet06PlacedProjection
open Packet06PlacedGreenObservation Packet06PlacedGreenSupport Packet06PlacedGreenPairing
open Packet06ProjectedGreen Packet06ProjectedPhysicalResidue Packet06SectorOperator Packet06MaterialSector
open Packet06RankOneRepair Packet06PhysicalNormalization KernelReciprocity
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

def transported (c : StaticCoefficient.Coefficient) (S J T U : ℝ)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (w : ℂ) : V →L[ℂ] BallL2 U :=
  ((s : ℂ)^2)⁻¹ • ((transport s hs a T U).comp
    ((projectedGreen c S J T (w/(s : ℂ))).comp (placed s hs a).symm.toContinuousLinearMap))

/-- Actual source/observation transport gives the physically normalized pole
coefficient at the scaled frequency; this theorem concerns the transported
operator and does not itself assert a transported Maxwell equation. -/
theorem transported_residue (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T U : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (hobs : s*(U+‖a‖) ≤ T)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ Q : V →L[ℂ] BallL2 U,
      (∀ f, (∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall a (J/s) → f (VectorFourier.coordinateMap x) = 0) →
        Q f = (-(∫ x : Maxwell.Space, ∑ i : Fin 3, f (VectorFourier.coordinateMap x) i *
          (placed s hs a (Packet06LocalPencil.response c z S J u)) (VectorFourier.coordinateMap x) i) /
          (2*((s : ℂ)*z))) •
          ConicalBallRestriction.vector U (placed s hs a (Packet06LocalPencil.response c z S T u))) ∧
      Tendsto (fun v => (v-(s : ℂ)*z) • transported c S J T U s hs a v)
        (𝓝[≠] ((s : ℂ)*z)) (𝓝 Q) := by
  obtain ⟨R,hR,hlim⟩ := projected_green_physical_residue c ha hm S J T hS hJ hST hc z hz u w ψ hC hu hψ hd hN
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  let L : (V →L[ℂ] BallL2 T) →L[ℂ] (V →L[ℂ] BallL2 U) :=
    ((ContinuousLinearMap.compL ℂ V (BallL2 T) (BallL2 U)) (transport s hs a T U)).comp
      ((ContinuousLinearMap.compL ℂ V V (BallL2 T)).flip (placed s hs a).symm.toContinuousLinearMap)
  have hmap : Tendsto (fun v : ℂ => v/(s : ℂ)) (𝓝[≠] ((s : ℂ)*z)) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h := ((continuous_id.div_const (s : ℂ)).tendsto ((s : ℂ)*z)).mono_left
        (show 𝓝[≠] ((s : ℂ)*z) ≤ 𝓝 ((s : ℂ)*z) from nhdsWithin_le_nhds)
      simpa [mul_comm, hs0] using h
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hv ⊢
      intro he
      apply hv
      apply (div_eq_iff hs0).mp at he
      simpa only [mul_comm] using he
  have ht := L.continuous.continuousAt.tendsto.comp (hlim.comp hmap)
  have hscaled := tendsto_const_nhds.smul ht (c := (s : ℂ)⁻¹)
  refine ⟨(s : ℂ)⁻¹ • L R,?_,?_⟩
  · intro f hf
    have hfb := inverse_source_supported s hs a (J/s) f hf
    have hj : s*(J/s)=J := mul_div_cancel₀ J hs.ne'
    rw [hj] at hfb
    have hr := hR ((placed s hs a).symm f) hfb
    change (s : ℂ)⁻¹ • transport s hs a T U (R ((placed s hs a).symm f)) = _
    rw [hr,map_smul,smul_smul,transport_restriction s hs a T U hobs]
    have hp := placed_pair s hs a ((placed s hs a).symm f) (Packet06LocalPencil.response c z S J u)
    rw [(placed s hs a).apply_symm_apply] at hp
    rw [Packet06PhysicalPairing.vectorPair_physical,Packet06PhysicalPairing.vectorPair_physical] at hp
    rw [← hp]
    congr 1
    field_simp [hs0,hz]
    exact Or.inl (by ring)
  · have he (v : ℂ) : (v-(s : ℂ)*z) • transported c S J T U s hs a v =
        (s : ℂ)⁻¹ • L ((v/(s : ℂ)-z) • projectedGreen c S J T (v/(s : ℂ))) := by
      have hscl : (v-(s : ℂ)*z) * (((s : ℂ)^2)⁻¹) = (s : ℂ)⁻¹ * (v/(s : ℂ)-z) := by
        field_simp [hs0]
        exact Or.inl (by ring)
      simp only [transported,L,map_smul,ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.smul_comp,smul_smul]
      rw [hscl]
      rfl
    simpa only [he] using hscaled

#print axioms OQ14.Packet06PlacedGreenResidue.transported_residue
end OQ14.Packet06PlacedGreenResidue
