import ModalDrivenProfiles

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ModalDrivenClassical
open Complex Filter OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ModalWronskian
  OQ14.ModalDipole OQ14.ModalInterface OQ14.ModalOrigin OQ14.ModalProfiles OQ14.ModalDriven
open MeasureTheory Set OQ14.RadialInterface OQ14.ModalDrivenProfiles
open scoped Topology

theorem outer_differentiable (k b : ℂ) (hk : k ≠ 0) (x : Space) (hx : x ≠ 0) :
    (∀ j, DifferentiableAt ℝ (fun y => outerE k b y j) x) ∧
    (∀ j, DifferentiableAt ℝ (fun y => outerH k b y j) x) := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hz := mul_ne_zero hk hrc
  have hu := scaledRadial_hasDerivAt (xi 1) (xiD 1) k ‖x‖ (xi_hasDerivAt 1 _ hz)
  have hsecond : HasDerivAt (xiD 1)
      ((2 / (k * ‖x‖)^2 - 1) * xi 1 (k * ‖x‖)) (k * ‖x‖) := by
    simpa only [Nat.cast_one, one_add_one_eq_two, one_mul] using xiD_hasDerivAt 1 (k * ‖x‖) hz
  have hv := scaledRadialD_hasDerivAt (xi 1) (xiD 1) k hk ‖x‖ hr hsecond
  constructor <;> intro j
  · exact (dipoleE_differentiableAt _ _ _ x hx hu hv j).const_mul b
  · exact (dipoleH_differentiableAt k k _ _ x hx hu j).const_mul b

theorem classical_maxwell (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (x : Space) (hx : ‖x‖ ≠ 1) :
    ComplexMaxwellAt k (coefficient n x) (electric n k) (magnetic n k) x := by
  rcases hx.lt_or_lt with hx | hx
  · have he : electric n k =ᶠ[𝓝 x] entireInnerE n k (numerator n k).1 := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
      simp [OQ14.ModalDriven.electric, entireInnerE, hy.le]
    have hh : magnetic n k =ᶠ[𝓝 x] entireInnerH n k (numerator n k).1 := by
      filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
      simp [OQ14.ModalDriven.magnetic, entireInnerH, hy.le]
    have hm := entireInner_maxwell n k (numerator n k).1 hn hk x
    constructor
    · rw [curl_eventuallyEq _ _ x he, hm.1]
      simp [OQ14.ModalDriven.magnetic, entireInnerH, hx.le]
    · rw [curl_eventuallyEq _ _ x hh, hm.2]
      simp [OQ14.ModalDriven.electric, coefficient, entireInnerE, hx.le]
  · have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
    let E₁ : Field := fun y => determinant n k • centerE k y
    let H₁ : Field := fun y => determinant n k • centerH k k y
    let E₂ : Field := outerE k (numerator n k).2
    let H₂ : Field := outerH k (numerator n k).2
    have he : electric n k =ᶠ[𝓝 x] (fun y => E₁ y + E₂ y) := by
      filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
      simp [OQ14.ModalDriven.electric, E₁, E₂, outerE, not_le.mpr hy]
    have hh : magnetic n k =ᶠ[𝓝 x] (fun y => H₁ y + H₂ y) := by
      filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
      simp [OQ14.ModalDriven.magnetic, H₁, H₂, outerH, not_le.mpr hy]
    have hdE : ∀ j, DifferentiableAt ℝ (fun y => E₁ y j) x := fun j =>
      (centerE_differentiableAt k x j).const_mul _
    have hdH : ∀ j, DifferentiableAt ℝ (fun y => H₁ y j) x := fun j =>
      (centerH_differentiableAt k k x j).const_mul _
    have ho := outer_differentiable k (numerator n k).2 hk x hx0
    have h₁ : ComplexMaxwellAt k 1 E₁ H₁ x :=
      complexMaxwell_scale k 1 (determinant n k) _ _ x
        (centerE_differentiableAt k x) (centerH_differentiableAt k k x)
        (center_maxwell k k 1 hk hk (by ring) x)
    have h₂ := outer_maxwell k (numerator n k).2 hk x hx0
    constructor
    · rw [curl_eventuallyEq _ _ x he]
      change curl (fun y j => E₁ y j + E₂ y j) x = _
      rw [curl_add _ _ x hdE ho.1, h₁.1, h₂.1]
      ext j
      simp [OQ14.ModalDriven.magnetic, H₁, H₂, outerH, not_le.mpr hx]
      ring
    · rw [curl_eventuallyEq _ _ x hh]
      change curl (fun y j => H₁ y j + H₂ y j) x = _
      rw [curl_add _ _ x hdH ho.2, h₁.2, h₂.2]
      ext j
      simp [OQ14.ModalDriven.electric, coefficient, E₁, E₂, outerE, not_le.mpr hx]
      ring

theorem weak_maxwell (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (OQ14.ModalDriven.electric n k) φ =
      (fun j => ∫ x, (I*k*OQ14.ModalDriven.magnetic n k x j)*φ x) ∧
    weakCurlPairing (OQ14.ModalDriven.magnetic n k) φ =
      (fun j => ∫ x, (-I*k*coefficient n x*OQ14.ModalDriven.electric n k x j)*φ x) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  constructor
  · rw [electric_weakCurl_eq_axial n k hn hk φ hφ hc,
      ← OQ14.RadialInterface.curl_integration_by_parts 1 _ (axial_continuous n k hn hk)
        (axial_differentiableAt n k hk) (axial_partial_locallyIntegrable n k hk) φ hφ1 hc]
    ext j
    apply integral_congr_ae
    filter_upwards [ae_regular 1] with x hx
    rw [← electric_curl_eq_axial n k hk x hx.1 hx.2,
      (classical_maxwell n k hn hk x hx.2).1]
  · rw [← OQ14.RadialInterface.curl_integration_by_parts 1 _
      (magnetic_continuous n k hn hk) (magnetic_differentiableAt n k hk)
      (magnetic_partial_locallyIntegrable n k hn hk) φ hφ1 hc]
    ext j
    apply integral_congr_ae
    filter_upwards [ae_regular 1] with x hx
    rw [(classical_maxwell n k hn hk x hx.2).2]

#print axioms OQ14.ModalDrivenClassical.weak_maxwell
#print axioms OQ14.ModalDrivenClassical.classical_maxwell
end OQ14.ModalDrivenClassical



