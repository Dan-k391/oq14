import Packet06PlacedGreenOutgoing
import Packet06PlacedGreenResidue
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.Packet06PlacedGreenIdentification
open MeasureTheory Metric Set Maxwell Packet06PlacedEquivalence Packet06PlacedGreenObservation
open Packet06PlacedGreenResidue Packet06CyclicRotation Packet06CyclicRotationMaxwell
open Packet06ProjectedGreen
open scoped Topology
abbrev V := VectorFourier.VectorL2

/-- The transported Green output is the restriction of the actual global field. -/
theorem restriction_ae (c : StaticCoefficient.Coefficient) (S J T U : ℝ)
    (hST : S+1 ≤ T) (hJT : J+1 ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (s : ℝ) (hs : 0 < s) (a : Space) (hobs : s*(U+‖a‖) ≤ T)
    (z : ℂ) (f : V)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J →
      ((placed s hs a).symm f) (VectorFourier.coordinateMap x) = 0) (i : Fin 3) :
    (fun x : Space => (transported c S J T U s hs a ((s : ℂ)*z) f i :
      ConicalRungeBall.ScalarBall U) x) =ᵐ[volume.restrict (closedBall 0 U)]
    fun x => (((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) * rotateField
      (Packet06ProjectedGlobal.field c S J z ((placed s hs a).symm f)) (s • (x-a)) i := by
  let g := (placed s hs a).symm f
  let F := projectedField c S J T z g
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have ht : transported c S J T U s hs a ((s : ℂ)*z) f =
      ((s : ℂ)^2)⁻¹ • ConicalBallRestriction.vector U (placed s hs a F) := by
    simp only [transported, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    have hz : ((s : ℂ)*z)/(s : ℂ) = z := by field_simp
    rw [hz]
    change ((s : ℂ)^2)⁻¹ • transport s hs a T U (projectedGreen c S J T z g) = _
    rw [← projected_restriction c S J T z g, transport_restriction s hs a T U hobs F]
  let q : Space → Space := fun x => unrotate (s • (x-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hlocal := (ae_restrict_iff' measurableSet_closedBall).mp
    (Packet06ProjectedGlobal.field_matches_local c S J T hST hJT z g hc hf (WeakCurl.previous i))
  have hlocal' := hq.ae hlocal
  have hsm := Lp.coeFn_smul (((s : ℂ)^2)⁻¹) (ConicalBallRestriction.vector U (placed s hs a F) i)
  rw [ht]
  filter_upwards [hsm,ConicalBallRestriction.vector_ae U (placed s hs a F) i,
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (placed s hs a F) i),
    ae_restrict_of_ae (Packet06PlacedAction.placed_unknown_ae s hs a F i),
    ae_restrict_of_ae hlocal',ae_restrict_mem measurableSet_closedBall] with x hsm hr hcoord hact hloc hx
  have hqT : q x ∈ closedBall (0 : Space) T := by
    have hxU : ‖x‖ ≤ U := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hdist : ‖x-a‖ ≤ U+‖a‖ := (norm_sub_le x a).trans (add_le_add_right hxU _)
    have hqnorm : ‖q x‖ = s*‖x-a‖ := by
      change ‖rotation.symm (s • (x-a))‖ = _
      rw [rotation.symm.norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    simp only [mem_closedBall,dist_zero_right]
    rw [hqnorm]
    exact (mul_le_mul_of_nonneg_left hdist hs.le).trans hobs
  change (((s : ℂ)^2)⁻¹ • (ConicalBallRestriction.vector U (placed s hs a F) i) :
    ConicalRungeBall.ScalarBall U) x = _
  rw [hsm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hr,hcoord,placed_apply,hact,← hloc hqT]
  simp only [Pi.smul_apply, smul_eq_mul,rotateField,q]
  ring

#print axioms OQ14.Packet06PlacedGreenIdentification.restriction_ae
end OQ14.Packet06PlacedGreenIdentification
