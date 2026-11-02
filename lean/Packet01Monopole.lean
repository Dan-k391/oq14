import MonopoleFlux
import WeakDerivativeIdentification
import KernelRadialMomentBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet01Monopole
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
  OQ14.ComplexKernelResponse OQ14.ExteriorHelmholtz OQ14.RadialNormTest
open scoped Topology

theorem regular_zero_of_flux (k c : ℂ) (hk : k ≠ 0) (F : ℝ → ℂ)
    (hrep : F =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun r => c * RadialOriginSelection.regular 0 k r))
    (hflux : ∀ η : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) 1 →
      (∫ r in Ioi (0 : ℝ), deriv η r * F r) = 0) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), F r = 0 := by
  let f : ℝ → ℂ := fun r => c * RadialOriginSelection.regular 0 k r
  let df : ℝ → ℂ := fun r => c * RadialOriginSelection.regularD 0 k r
  have hf (r : ℝ) (_ : r ∈ Ioo (0 : ℝ) 1) : HasDerivAt f (df r) r :=
    (RadialOriginSelection.regular_hasDerivAt 0 k r).const_mul c
  have hd : ContinuousOn df (Ioo (0 : ℝ) 1) := by
    intro r hr
    exact ((RadialOriginSelection.regularD_hasDerivAt 0 k hk r hr.1.ne').const_mul c).continuousAt.continuousWithinAt
  have hw : SmoothWeakDerivative.WeakDerivative (Ioo (0 : ℝ) 1) f (fun _ => 0) := by
    intro η hη hc hs
    let θ : ℝ → ℂ := fun r => (η r : ℂ)
    have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := Complex.ofRealCLM.contDiff.comp hη
    have hθc : HasCompactSupport θ := hc.comp_left (by simp : Complex.ofReal 0 = 0)
    have hθs : tsupport θ ⊆ Ioo (0 : ℝ) 1 := by
      have : tsupport θ = tsupport η := by
        apply congrArg closure
        ext x
        exact not_congr Complex.ofReal_eq_zero
      rwa [this]
    have hdθ (r : ℝ) : deriv θ r = ((deriv η r : ℝ) : ℂ) :=
      ((hη.differentiable (by simp) r).hasDerivAt.ofReal_comp).deriv
    have hsder (r : ℝ) (hr : r ∉ Ioo (0 : ℝ) 1) : deriv θ r = 0 :=
      Function.nmem_support.mp (fun h => hr (hθs (support_deriv_subset h)))
    have hrestrict : (∫ r, deriv θ r * f r) = ∫ r in Ioo (0 : ℝ) 1, deriv θ r * f r := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo (0 : ℝ) 1
      · simp [hr]
      · simp [hr, hsder r hr]
    have hrestrict' : (∫ r in Ioi (0 : ℝ), deriv θ r * F r) =
        ∫ r in Ioo (0 : ℝ) 1, deriv θ r * F r := by
      rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo (0 : ℝ) 1
      · have hr' : r ∈ Ioi (0 : ℝ) := hr.1
        simp [hr, hr']
      · simp [hr, hsder r hr]
    have heq : (∫ r in Ioo (0 : ℝ) 1, deriv θ r * f r) =
        ∫ r in Ioo (0 : ℝ) 1, deriv θ r * F r := by
      apply integral_congr_ae
      filter_upwards [hrep] with r hr
      rw [hr]
    have h := hflux θ hθ hθc hθs
    rw [hrestrict'] at h
    simp only [mul_zero, integral_zero, add_zero]
    simp_rw [← hdθ]
    rw [hrestrict, heq]
    exact h
  have hd0 := WeakDerivativeIdentification.classical (Ioo (0 : ℝ) 1) isOpen_Ioo f df
    (fun _ => 0) hf hd (continuousOn_const.locallyIntegrableOn measurableSet_Ioo) hw
  have hpoint : ∀ r ∈ Ioo (0 : ℝ) 1, df r = 0 :=
    Measure.eqOn_open_of_ae_eq hd0.symm isOpen_Ioo hd continuousOn_const
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with r hr hri
  have he : df =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hri] with t ht
    exact hpoint t ht
  have hder := ((RadialOriginSelection.regularD_hasDerivAt 0 k hk r hri.1.ne').const_mul c).congr_of_eventuallyEq he.symm
  have hz := hder.unique (hasDerivAt_const r (0 : ℂ))
  have hz' : -(k^2) * (c * RadialOriginSelection.regular 0 k r) = 0 := by
    simp only [RadialRellich.radialCoefficient, Nat.cast_ofNat, zero_mul, zero_div, zero_sub] at hz
    linear_combination hz
  have hreg : c * RadialOriginSelection.regular 0 k r = 0 :=
    (mul_eq_zero.mp hz').resolve_left (neg_ne_zero.mpr (pow_ne_zero 2 hk))
  exact hr.trans hreg

theorem monopole_radial_coefficient_eq_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (1 : Poly) r = 0 := by
  let A := ComplexKernelDebye.radialCoefficient n hn z u (1 : Poly)
  let B := radialMoment (ComplexKernelDebye.coordinates n hn z u) (1 : Poly)
  let F : ℝ → ℂ := fun r => (r : ℂ)^2 * A r
  have hk : z * (n : ℂ) ≠ 0 := mul_ne_zero hz (Complex.ofReal_ne_zero.mpr (by linarith))
  obtain ⟨c, hc⟩ := ComplexKernelDebye.regular_radial_coefficient n hn z hz u hker
    (1 : Poly) 0 (MvPolynomial.isHomogeneous_one (Fin 3) ℝ) (by simp [formalLaplacian_apply])
  have hb := KernelRadialMomentBridge.radial_moment_actual n hn z u (1 : Poly)
  have hflux : ∀ η : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) 1 → (∫ r in Ioi (0 : ℝ), deriv η r * F r) = 0 := by
    intro η hη hηc hηs
    have hzder (r : ℝ) (hr : r ∉ Ioo (0 : ℝ) 1) : deriv η r = 0 :=
      Function.nmem_support.mp (fun h => hr (hηs (support_deriv_subset h)))
    have restrict_test (G : ℝ → ℂ) : (∫ r in Ioi (0 : ℝ), deriv η r * G r) =
        ∫ r in Ioo (0 : ℝ) 1, deriv η r * G r := by
      rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo (0 : ℝ) 1
      · have hr' : r ∈ Ioi (0 : ℝ) := hr.1
        simp [hr, hr']
      · simp [hr, hzder r hr]
    have h := MonopoleFlux.actual_weak_flux n hn z hz u hker η hη hηc hηs
    have h' : (∫ r in Ioi (0 : ℝ), deriv η r * ((r : ℂ)^2 * B r)) = 0 := by
      convert h using 1
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [restrict_test] at h' ⊢
    apply Eq.trans ?_ h'
    apply integral_congr_ae
    filter_upwards [hb] with r hr
    change deriv η r * ((r : ℂ)^2 * A r) = deriv η r * ((r : ℂ)^2 * B r)
    change B r = A r at hr
    rw [hr]
  have hzF := regular_zero_of_flux (z*n) c hk F hc hflux
  filter_upwards [hzF, ae_restrict_mem measurableSet_Ioo] with r hr hri
  exact (mul_eq_zero.mp hr).resolve_left (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hri.1.ne'))

#print axioms OQ14.Packet01Monopole.regular_zero_of_flux
#print axioms OQ14.Packet01Monopole.monopole_radial_coefficient_eq_zero
end OQ14.Packet01Monopole
