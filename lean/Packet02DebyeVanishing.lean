import Packet02MagneticVanishing

/-! The actual magnetic Debye datum vanishes, and its covariance representative
is locally square-integrable on every closed ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02DebyeVanishing
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ModalWeightedMode
open OQ14.ModalMeridionalReflection OQ14.WeakDebyeScalar

theorem datum_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) :
    DebyeScalarL2.datum 1 (ComplexMagneticDebye.coordinates n hn z u) = 0 := by
  apply MeasureTheory.Lp.ext
  have hc : ∀ᵐ x ∂(volume : Measure Space), x ∈ closedBall 0 1 →
      ∀ j, ComplexMagneticDebye.coordinates n hn z u j x = ComplexSphereMaxwell.magnetic n hn z u x j :=
    ae_restrict_iff' measurableSet_closedBall |>.mp <| ae_all_iff.mpr (fun j =>
      ComplexMagneticResponse.response_actual (coefficient n hn) z 1 1 u (coefficient_support n hn) j)
  filter_upwards [DebyeScalarL2.datum_actual 1 (ComplexMagneticDebye.coordinates n hn z u),
    hc, Packet02MagneticVanishing.radial_zero_ae n hn u hu z, Lp.coeFn_zero ℂ 2 volume] with x hd hc hr hz
  rw [hd, hz]
  by_cases hx : x ∈ closedBall (0 : Space) 1
  · rw [DebyeScalarL2.clipped, indicator_of_mem hx]
    convert hr using 1
    unfold radialDot
    apply Finset.sum_congr rfl
    intro j hj
    change (x j : ℂ) * ComplexMagneticDebye.coordinates n hn z u j x = _
    rw [hc hx j]
  · simp [DebyeScalarL2.clipped, hx]

theorem representative_memLp_ball (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (R : ℝ) (i : Fin 3) :
    MemLp (fun x => Packet02MagneticVanishing.representative n hn z u x i) 2
      (volume.restrict (closedBall 0 R)) := by
  have hm := ComplexMagneticLocal.magnetic_memLp_ball z R 1
    (StaticCoefficient.sqrtMultiplier (coefficient n hn) u) (DynamicVolume.source (coefficient n hn) u)
    (DynamicVolume.source_integrable _ u 1 (coefficient_support n hn))
    (DynamicVolume.source_zero _ u 1 (coefficient_support n hn))
    (StaticNewton.material_source_ae _ u) i
  apply hm.ae_eq
  filter_upwards [ae_restrict_of_ae (Packet02MagneticVanishing.representative_ae n hn z u)] with x hx
  exact (congrFun hx i).symm

#print axioms OQ14.Packet02DebyeVanishing.datum_zero
#print axioms OQ14.Packet02DebyeVanishing.representative_memLp_ball
end OQ14.Packet02DebyeVanishing
