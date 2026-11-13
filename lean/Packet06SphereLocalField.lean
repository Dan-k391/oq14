import Packet06CertifiedSphere

/-! The actual sphere response has the explicit regular dipole interior and
a nonzero axial component on a genuine neighborhood of the center. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06SphereLocalField
open MeasureTheory Filter Metric Packet06SectorOperator
open scoped Topology

def inner (n : ℝ) (z a : ℂ) : Maxwell.Field :=
  fun x i => a * (Complex.I/(n : ℂ)) * ModalOrigin.centerE ((n : ℂ)*z) x i

theorem response_inner_ae (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) (i : Fin 3) :
    (fun x : Maxwell.Space => Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn)
      z 1 T (numerator n hn z) (VectorFourier.coordinateMap x) i) =ᵐ[volume.restrict (ball 0 1)]
      fun x => inner n z 1 x i := by
  let c := ModalWeightedMode.coefficient n hn
  let F := Packet06LocalPencil.response c z 1 T (numerator n hn z)
  have hw : StaticCoefficient.sqrtMultiplier c F = (numerator n hn z : VectorL2) := by
    rw [Packet06Observation.weighted_observation_independent c z 1 T hT _
      (ModalWeightedMode.coefficient_support n hn)]
    exact (Packet06LocalPencil.actual_kernel_transport c z 1 _
      (ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hdet).2).2
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c F)
  rw [hw] at hm
  filter_upwards [ae_restrict_of_ae hm,ae_restrict_of_ae (ModalVolumeData.numerator_actual n hn z i),
    ae_restrict_mem measurableSet_ball] with x hx hu hball
  have hnorm : ‖x‖ < 1 := by simpa using hball
  have hs : (Real.sqrt (n^2-1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (ModalWeightedMode.contrast_pos n hn)).ne'
  have hxi := congrArg (fun v : VectorFourier.Vector => v i) hx
  change ModalVolumeData.numerator n hn z (VectorFourier.coordinateMap x) i =
    (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * F (VectorFourier.coordinateMap x) i at hxi
  rw [hu] at hxi
  change (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
    ((Complex.I/(n : ℂ))*ModalOrigin.centerE ((n : ℂ)*z) x i) =
    (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) * F (VectorFourier.coordinateMap x) i at hxi
  rw [ModalWeightedMode.coefficient_value,if_pos hnorm] at hxi
  have he := mul_left_cancel₀ hs hxi
  simpa only [inner,one_mul] using he.symm

theorem axial_nonzero_near_center (n : ℝ) (hn : 1 < n) (z a : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : Maxwell.Space, ‖x‖ < r → inner n z a x 2 ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h0 : inner n z a 0 2 ≠ 0 := by
    change a * (Complex.I/(n : ℂ)) * ModalOrigin.centerE ((n : ℂ)*z) 0 2 ≠ 0
    rw [ModalOrigin.centerE_zero]
    exact mul_ne_zero (mul_ne_zero ha (div_ne_zero Complex.I_ne_zero hn0))
      (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero hn0 hz))) (by norm_num))
  have hc : Continuous (fun x : Maxwell.Space => inner n z a x 2) :=
    continuous_const.mul (ModalOrigin.centerE_continuous ((n : ℂ)*z) 2)
  have he := hc.continuousAt.tendsto.eventually_ne h0
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min δ (1/2),lt_min hδ (by norm_num),(min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro x hx
  apply hball
  simpa only [dist_zero_right] using hx.trans_le (min_le_left _ _)

end OQ14.Packet06SphereLocalField
#print axioms OQ14.Packet06SphereLocalField.response_inner_ae
#print axioms OQ14.Packet06SphereLocalField.axial_nonzero_near_center
