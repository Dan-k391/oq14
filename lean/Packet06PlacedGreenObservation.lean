import Packet06PlacedGreenSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PlacedGreenObservation
open MeasureTheory Metric Set Maxwell Packet06PlacedEquivalence Packet06PlacedProjection
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

def transport (s : ℝ) (hs : 0 < s) (a : Space) (T U : ℝ) : BallL2 T →L[ℂ] BallL2 U :=
  (ConicalBallRestriction.vector U).comp ((placed s hs a).toContinuousLinearMap.comp (ConicalBallExtension.vector T))

/-- Extending a base-ball field by zero before the actual placement does not
alter the observation on a target ball whose inverse image lies in that ball. -/
theorem transport_restriction (s : ℝ) (hs : 0 < s) (a : Space) (T U : ℝ)
    (hbound : s*(U+‖a‖) ≤ T) (F : V) :
    transport s hs a T U (ConicalBallRestriction.vector T F) =
      ConicalBallRestriction.vector U (placed s hs a F) := by
  let G := ConicalBallExtension.vector T (ConicalBallRestriction.vector T F)
  have hlocal (i : Fin 3) : ∀ᵐ x : Space ∂volume, x ∈ closedBall 0 T →
      G (VectorFourier.coordinateMap x) i = F (VectorFourier.coordinateMap x) i := by
    have he := ConicalBallExtension.vector_ae T (ConicalBallRestriction.vector T F) i
    have hr := (ae_restrict_iff' measurableSet_closedBall).mp
      (ConicalBallRestriction.vector_ae T F i)
    filter_upwards [he,hr,NewtonL2.physicalCoordinate_ae G i,NewtonL2.physicalCoordinate_ae F i] with x he hr hg hf hx
    rw [← hg,he,indicator_of_mem hx,hr hx,hf]
  let q : Space → Space := fun x => Packet06CyclicRotation.unrotate (s • (x-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := Packet06CyclicRotation.rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hloc := hq.ae (ae_all_iff.mpr hlocal)
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [ConicalBallRestriction.vector_ae U (placed s hs a G) i,
    ConicalBallRestriction.vector_ae U (placed s hs a F) i,
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (placed s hs a G) i),
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (placed s hs a F) i),
    ae_restrict_of_ae (Packet06PlacedAction.placed_unknown_ae s hs a G i),
    ae_restrict_of_ae (Packet06PlacedAction.placed_unknown_ae s hs a F i),
    ae_restrict_of_ae hloc,ae_restrict_mem measurableSet_closedBall] with x hg hf hcg hcf hpq hpf hloc hx
  change (ConicalBallRestriction.vector U (placed s hs a G) i : ConicalRungeBall.ScalarBall U) x = _
  rw [hg,hf,hcg,hcf,placed_apply,placed_apply,hpq,hpf]
  have hqT : q x ∈ closedBall (0 : Space) T := by
    have hxU : ‖x‖ ≤ U := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hdist : ‖x-a‖ ≤ U+‖a‖ := (norm_sub_le x a).trans (add_le_add_right hxU _)
    have hqnorm : ‖q x‖ = s*‖x-a‖ := by
      change ‖Packet06CyclicRotation.rotation.symm (s • (x-a))‖ = _
      rw [Packet06CyclicRotation.rotation.symm.norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    simp only [mem_closedBall,dist_zero_right]
    rw [hqnorm]
    exact (mul_le_mul_of_nonneg_left hdist hs.le).trans hbound
  change _ * G (VectorFourier.coordinateMap (q x)) _ = _ * F (VectorFourier.coordinateMap (q x)) _
  rw [hloc _ hqT]

#print axioms OQ14.Packet06PlacedGreenObservation.transport_restriction
end OQ14.Packet06PlacedGreenObservation
