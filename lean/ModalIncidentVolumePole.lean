import ModalVolumeDerivativePairing
import ModalSphereVolumePoles

/-! Exact simple pole of the full volume inverse applied to the actual analytic
regular-dipole incident datum. This is a driven vector response, not a claim
about the order or rank of the whole inverse operator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ModalIncidentVolumePole
open Complex Filter OQ14.ModalVolumeData OQ14.ComplexConvolutionAnalytic
open scoped Topology

def response (n : ℝ) (hn : 1 < n) (z : ℂ) : VectorFourier.VectorL2 :=
  Ring.inverse (volumeBlock (ModalWeightedMode.coefficient n hn) z 1) (incident n hn z)

def quotient (n : ℝ) (hn : 1 < n) (z : ℂ) : VectorFourier.VectorL2 :=
  (ModalDipoleOrigin.regularized (n : ℂ) z)⁻¹ • numerator n hn z

def regularized (n : ℝ) (hn : 1 < n) (z₀ z : ℂ) : VectorFourier.VectorL2 :=
  (dslope (ModalDipoleOrigin.regularized (n : ℂ)) z₀ z)⁻¹ • numerator n hn z

theorem response_eq_quotient (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hu : IsUnit (volumeBlock (ModalWeightedMode.coefficient n hn) z 1))
    (hd : ModalDipoleOrigin.regularized (n : ℂ) z ≠ 0) :
    response n hn z = quotient n hn z := by
  let A := volumeBlock (ModalWeightedMode.coefficient n hn) z 1
  have h := congrArg (fun v => Ring.inverse A v)
    (ModalSphereVolumeKernel.complex_volume_identity n hn z)
  have hi := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 =>
    L (numerator n hn z)) (Ring.inverse_mul_cancel A hu)
  change Ring.inverse A (A (numerator n hn z)) = numerator n hn z at hi
  change Ring.inverse A (A (numerator n hn z)) =
    Ring.inverse A (ModalDipoleOrigin.regularized (n : ℂ) z • incident n hn z) at h
  rw [hi, map_smul] at h
  change numerator n hn z = ModalDipoleOrigin.regularized (n : ℂ) z • response n hn z at h
  rw [quotient, h, inv_smul_smul₀ hd]

theorem slope_analytic (n : ℝ) (z : ℂ) :
    AnalyticAt ℂ (dslope (ModalDipoleOrigin.regularized (n : ℂ)) z) z := by
  obtain ⟨p, hp⟩ := ModalDipoleOrigin.regularized_analyticAt (n : ℂ) z
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem regularized_analytic (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hs : deriv (ModalDipoleOrigin.regularized (n : ℂ)) z ≠ 0) :
    AnalyticAt ℂ (regularized n hn z) z :=
  ((slope_analytic n z).inv (by simpa only [dslope_same] using hs)).smul
    (numerator_analytic n hn z)

theorem quotient_normal_form (n : ℝ) (hn : 1 < n) (z w : ℂ)
    (hd : ModalDipoleOrigin.regularized (n : ℂ) z = 0) (hw : w ≠ z) :
    quotient n hn w = (w-z)⁻¹ • regularized n hn z w := by
  simp only [quotient, regularized, dslope_of_ne _ hw, slope_def_field, hd, sub_zero,
    inv_div, smul_smul]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hw), one_mul]

theorem response_eventually_quotient (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hd : ModalDipoleOrigin.regularized (n : ℂ) z = 0)
    (hs : deriv (ModalDipoleOrigin.regularized (n : ℂ)) z ≠ 0) :
    response n hn =ᶠ[𝓝[≠] z] quotient n hn := by
  have he : ∀ᶠ w in 𝓝 z, dslope (ModalDipoleOrigin.regularized (n : ℂ)) z w ≠ 0 :=
    (slope_analytic n z).continuousAt.eventually_ne (by simpa only [dslope_same] using hs)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    ModalSphereVolumePoles.punctured_invertibility n hn z] with w hw hwz hu
  apply response_eq_quotient n hn w hu
  have hf : ModalDipoleOrigin.regularized (n : ℂ) w =
      (w-z)*dslope (ModalDipoleOrigin.regularized (n : ℂ)) z w := by
    rw [dslope_of_ne _ hwz, slope_def_field, hd, sub_zero]
    field_simp [sub_ne_zero.mpr hwz]
  rw [hf]
  exact mul_ne_zero (sub_ne_zero.mpr hwz) hw

theorem response_meromorphic (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hd : ModalDipoleOrigin.regularized (n : ℂ) z = 0)
    (hs : deriv (ModalDipoleOrigin.regularized (n : ℂ)) z ≠ 0) :
    MeromorphicAt (response n hn) z :=
  (((ModalDipoleOrigin.regularized_analyticAt (n : ℂ) z).meromorphicAt.inv).smul
    (numerator_analytic n hn z).meromorphicAt).congr
      (response_eventually_quotient n hn z hd hs).symm

theorem simple_pole_and_residue (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (hs : deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0) :
    (∃ hm : MeromorphicAt (response n hn) z, hm.order = (-1 : ℤ)) ∧
    Tendsto (fun w => (w-z) • response n hn w) (𝓝[≠] z)
      (𝓝 ((deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z)⁻¹ • numerator n hn z)) ∧
    (deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z)⁻¹ • numerator n hn z ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hd' : ModalDipoleOrigin.regularized (n : ℂ) z = 0 :=
    (ModalDipoleOrigin.regularized_eq _ _ hn0 hz).trans hd
  have hs' : deriv (ModalDipoleOrigin.regularized (n : ℂ)) z ≠ 0 := by
    rwa [ModalVolumeDerivativePairing.regularized_deriv _ _ hn0 hz]
  have ha := regularized_analytic n hn z hs'
  have hcenter : regularized n hn z z =
      (deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z)⁻¹ • numerator n hn z := by
    rw [regularized, dslope_same, ModalVolumeDerivativePairing.regularized_deriv _ _ hn0 hz]
  have hnon := smul_ne_zero (inv_ne_zero hs) (numerator_ne_zero n hn z hz)
  have he : ∀ᶠ w in 𝓝[≠] z, response n hn w = (w-z)⁻¹ • regularized n hn z w := by
    filter_upwards [response_eventually_quotient n hn z hd' hs', self_mem_nhdsWithin] with w hw hwz
    rw [hw, quotient_normal_form n hn z w hd' hwz]
  refine ⟨⟨response_meromorphic n hn z hd' hs', ?_⟩, ?_, hnon⟩
  · apply (MeromorphicAt.order_eq_int_iff _).mpr
    refine ⟨regularized n hn z, ha, hcenter ▸ hnon, ?_⟩
    simpa only [zpow_neg_one] using he
  · have ht := ha.continuousAt.tendsto.mono_left
      (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
    rw [hcenter] at ht
    apply ht.congr'
    filter_upwards [he, self_mem_nhdsWithin] with w hw hwz
    rw [hw, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hwz), one_smul]

end OQ14.ModalIncidentVolumePole

#print axioms OQ14.ModalIncidentVolumePole.response_eq_quotient
#print axioms OQ14.ModalIncidentVolumePole.slope_analytic
#print axioms OQ14.ModalIncidentVolumePole.regularized_analytic
#print axioms OQ14.ModalIncidentVolumePole.quotient_normal_form
#print axioms OQ14.ModalIncidentVolumePole.response_eventually_quotient
#print axioms OQ14.ModalIncidentVolumePole.response_meromorphic
#print axioms OQ14.ModalIncidentVolumePole.simple_pole_and_residue
