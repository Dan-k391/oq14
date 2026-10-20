import RadialMomentRegularity
import RadialMomentWeights
import OneDimensionalGreen

/-! # Classical radial equations from actual compact-test weak equations -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.RadialMomentClassical
open MeasureTheory Set OQ14.RadialMomentWeights OQ14.RadialMoment OQ14.RadialMomentRegularity

def radialFlux (UD : ℝ → ℂ) (r : ℝ) : ℂ := (r : ℂ)^2*UD r

theorem residual_of_weak (l : ℕ) (k : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (U UD UDD : ℝ → ℂ)
    (hU : ∀ r, R < r → HasDerivAt U (UD r) r)
    (hUD : ∀ r, R < r → HasDerivAt UD (UDD r) r)
    (hUDDc : ContinuousOn UDD (Ioi R))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi R →
      (∫ r : ℝ, coefficientA l U r*((deriv (deriv η) r : ℝ) : ℂ)+
        coefficientB l U r*((deriv η r : ℝ) : ℂ)+coefficientC l k U r*(η r : ℂ)) = 0) :
    ∀ r, R < r → (r : ℂ)^2*UDD r+2*(r : ℂ)*UD r+
      (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*U r = 0 := by
  have hUc : ContinuousOn U (Ioi R) := fun r hr => (hU r hr).continuousAt.continuousWithinAt
  have hUDc : ContinuousOn UD (Ioi R) := fun r hr => (hUD r hr).continuousAt.continuousWithinAt
  have hz := OneDimensionalGreen.weak_green_pointwise (Ioi R) isOpen_Ioi
    (coefficientA l U) (coefficientAD l U UD) (coefficientADD l U UD UDD)
    (coefficientB l U) (coefficientBD l U UD) (coefficientC l k U)
    (fun r hr => coefficientA_hasDerivAt l U UD r (hU r hr))
    (fun r hr => coefficientAD_hasDerivAt l U UD UDD r (hU r hr) (hUD r hr))
    (fun r hr => coefficientB_hasDerivAt l U UD r (hU r hr))
    (coefficientADD_continuousOn l _ U UD UDD hUc hUDc hUDDc)
    (coefficientBD_continuousOn l _ U UD hUc hUDc)
    (coefficientC_continuousOn l k _ U hUc) hweak
  intro r hr
  have heq := hz r hr
  rw [coefficient_residual] at heq
  exact (mul_eq_zero.mp heq).resolve_left
    (pow_ne_zero l (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt hR hr))))

theorem flux_hasDerivAt_of_residual (l : ℕ) (k : ℂ) (U UD UDD : ℝ → ℂ) (r : ℝ)
    (hUD : HasDerivAt UD (UDD r) r)
    (hres : (r : ℂ)^2*UDD r+2*(r : ℂ)*UD r+
      (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*U r = 0) :
    HasDerivAt (radialFlux UD) (((l : ℂ)*((l : ℂ)+1)-k^2*(r : ℂ)^2)*U r) r := by
  convert (complex_power_hasDerivAt 2 r).mul hUD using 1
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  linear_combination -hres

theorem derivative_eq_flux (UD : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0) :
    UD r = radialFlux UD r/(r : ℂ)^2 := by
  unfold radialFlux
  field_simp [Complex.ofReal_ne_zero.mpr hr]


theorem moment_classical_of_weak (l : ℕ) (k : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : OQ14.Maxwell.Space → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : OQ14.Maxwell.Space | R < ‖x‖})
    (P : OQ14.AngularPower.Sphere → ℂ) (hP : Continuous P)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi R →
      (∫ r : ℝ, coefficientA l (moment u P) r*((deriv (deriv η) r : ℝ) : ℂ)+
        coefficientB l (moment u P) r*((deriv η r : ℝ) : ℂ)+
          coefficientC l k (moment u P) r*(η r : ℂ)) = 0) :
    ∀ r, R < r →
      ((r : ℂ)^2*momentDD u P r+2*(r : ℂ)*momentD u P r+
        (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*moment u P r = 0) ∧
      HasDerivAt (radialFlux (momentD u P))
        (((l : ℂ)*((l : ℂ)+1)-k^2*(r : ℂ)^2)*moment u P r) r ∧
      momentD u P r = radialFlux (momentD u P) r/(r : ℂ)^2 := by
  have hz := residual_of_weak l k R hR (moment u P) (momentD u P) (momentDD u P)
    (fun r hr => moment_hasDerivAt R r hR hr u hu P hP)
    (fun r hr => momentD_hasDerivAt R r hR hr u hu P hP)
    (momentDD_continuousOn R hR u hu P hP) hweak
  intro r hr
  exact ⟨hz r hr, flux_hasDerivAt_of_residual l k _ _ _ r
    (momentD_hasDerivAt R r hR hr u hu P hP) (hz r hr),
    derivative_eq_flux _ r (ne_of_gt (lt_of_le_of_lt hR hr))⟩
end OQ14.RadialMomentClassical

#print axioms OQ14.RadialMomentClassical.residual_of_weak
#print axioms OQ14.RadialMomentClassical.flux_hasDerivAt_of_residual
#print axioms OQ14.RadialMomentClassical.derivative_eq_flux
#print axioms OQ14.RadialMomentClassical.moment_classical_of_weak
