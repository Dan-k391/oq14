import ModalDipoleAngularProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalDipoleSlice
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalDipoleAngularProjection OQ14.ModalOrigin
open scoped Topology

theorem numerator_vector_ae (n : ℝ) (hn : 1 < n) (z : ℂ) :
    (fun x : Space => ModalVolumeData.numerator n hn z (VectorFourier.coordinateMap x)) =ᵐ[volume]
      fun x => ((Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        (I/(n : ℂ))) • (WithLp.equiv 2 (Fin 3 → ℂ)).symm (centerE ((n : ℂ)*z) x) := by
  have h := ae_all_iff.mpr (ModalVolumeData.numerator_actual n hn z)
  filter_upwards [h] with x hx
  apply PiLp.ext
  intro i
  rw [hx i]
  simp only [PiLp.smul_apply, smul_eq_mul, WithLp.equiv_symm_pi_apply]
  ring

theorem numerator_slice (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ModalVectorAngularSlices.slice (ModalVolumeData.numerator n hn z) r =
        ((Real.sqrt (n^2-1) : ℂ) * (I/(n : ℂ))) •
          ContinuousMap.toLp 2 angularMeasure ℂ (electricMap ((n : ℂ)*z) r) := by
  have hs := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)
    (ModalVectorAngularSlices.slice_actual_ae (ModalVolumeData.numerator n hn z))
  have hu := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)
    (PolarMomentAE.polar_ae (numerator_vector_ae n hn z))
  filter_upwards [hs, hu, ae_restrict_mem measurableSet_Ioo] with r hs hu hr
  apply Lp.ext
  filter_upwards [hs, hu, Lp.coeFn_smul ((Real.sqrt (n^2-1) : ℂ) * (I/(n : ℂ)))
      (ContinuousMap.toLp 2 angularMeasure ℂ (electricMap ((n : ℂ)*z) r)),
    (electricMap ((n : ℂ)*z) r).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with ω hs hu hsm he
  rw [hs, hu, hsm]
  simp only [Pi.smul_apply]
  rw [he, ModalWeightedMode.coefficient_value]
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr.1]
  simp [hnorm, hr.2, electricMap]

theorem numerator_slice_projected (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      projection (ModalVectorAngularSlices.slice (ModalVolumeData.numerator n hn z) r) =
        ModalVectorAngularSlices.slice (ModalVolumeData.numerator n hn z) r := by
  filter_upwards [numerator_slice n hn z, ae_restrict_mem measurableSet_Ioo] with r hr hri
  rw [hr, map_smul, dipole_slice_projected _ r hri.1]

#print axioms OQ14.ModalDipoleSlice.numerator_vector_ae
#print axioms OQ14.ModalDipoleSlice.numerator_slice
#print axioms OQ14.ModalDipoleSlice.numerator_slice_projected
end OQ14.ModalDipoleSlice

