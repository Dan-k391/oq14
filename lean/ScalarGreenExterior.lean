import ScalarGreenMoment
import ScalarFarField
import RadialBoundarySelection
import RadialMomentODE

/-! Actual outgoing selection of the exterior Green spherical moments. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.ScalarGreenExterior

open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.HarmonicPolynomial
  OQ14.RadialMoment OQ14.SphericalMomentEquation OQ14.ScalarGreenMoment
  OQ14.RadialMomentWeights OQ14.RadialMomentClassical OQ14.RadialRellich
open scoped Topology RealInnerProductSpace

def amplitude (k : ℝ) (y : Space) (p : Poly) : ℂ :=
  ∫ n : OQ14.AngularPower.Sphere,
    (Complex.exp (-Complex.I*k*(@inner ℝ Space _ (n : Space) y : ℝ))/(4*Real.pi))*angularPolynomial p n
    ∂OQ14.AngularPower.angularMeasure

theorem scaled_moment_integral (k r : ℝ) (y : Space) (p : Poly) :
    phase k r*((r : ℂ)*coefficient k y p r)=
      ∫ n : OQ14.AngularPower.Sphere,ScalarFarField.scaledKernel k r n y*angularPolynomial p n
        ∂OQ14.AngularPower.angularMeasure := by
  have hf : (fun n : OQ14.AngularPower.Sphere => ScalarFarField.scaledKernel k r n y*angularPolynomial p n)=
      fun n : OQ14.AngularPower.Sphere => (phase k r*(r : ℂ))*(kernel k y (r • (n : Space))*angularPolynomial p n) := by
    funext n
    simp only [ScalarFarField.scaledKernel,phase,kernel]
    ring
  rw [hf,integral_const_mul]
  unfold coefficient moment
  ring

theorem coefficient_scaled_limit (k : ℝ) (y : Space) (p : Poly) :
    Tendsto (fun r => phase k r*((r : ℂ)*coefficient k y p r)) atTop (𝓝 (amplitude k y p)) := by
  simp_rw [scaled_moment_integral]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun n : OQ14.AngularPower.Sphere => (2/(4*Real.pi))*‖angularPolynomial p n‖)
  · apply Eventually.of_forall
    intro r
    have hm : Measurable (fun n : OQ14.AngularPower.Sphere => phi k (r • (n : Space)-y)) :=
      (KernelIntegrability.phi_measurable k).comp
        ((measurable_const.smul measurable_subtype_coe).sub measurable_const)
    exact ((hm.const_mul ((r : ℂ)*Complex.exp (-Complex.I*k*r))).mul
      (angularPolynomial_continuous p).measurable).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (2*‖y‖)] with r hr
    filter_upwards with n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (ScalarFarField.scaledKernel_bound k ‖y‖ r (norm_nonneg _) hr n y
        (OQ14.AngularPower.sphere_norm n) (by simp)) (norm_nonneg _)
  · exact ((angularPolynomial_continuous p).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  · filter_upwards with n
    exact (ScalarFarField.scaledKernel_limit k n y (OQ14.AngularPower.sphere_norm n)).mul_const _

theorem exterior_flux_derivatives (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : ‖y‖ < r) :
    HasDerivAt (coefficient k y p)
      (radialFlux (momentD (kernel k y) (angularPolynomial p)) r/(r : ℂ)^2) r ∧
    HasDerivAt (radialFlux (momentD (kernel k y) (angularPolynomial p)))
      (((l : ℂ)*(l+1)-(k : ℂ)^2*(r : ℂ)^2)*coefficient k y p r) r := by
  have hr' : r ∈ Ioo ‖y‖ (r+1) := ⟨hr,by linarith⟩
  have hy : ‖y‖ ∉ Ioo ‖y‖ (r+1) := fun h => (lt_irrefl ‖y‖) h.1
  have hu := kernel_annular_smooth k y ‖y‖ (r+1) hy
  have hU := AnnularMoment.moment_hasDerivAt ‖y‖ (r+1) r (norm_nonneg _) hr'
    (kernel k y) hu (angularPolynomial p) (angularPolynomial_continuous p)
  have hUD := AnnularMoment.momentD_hasDerivAt ‖y‖ (r+1) r (norm_nonneg _) hr'
    (kernel k y) hu (angularPolynomial p) (angularPolynomial_continuous p)
  have hres := coefficient_classical_annulus k y p l hp hh ‖y‖ (r+1) (norm_nonneg _) hy r hr'
  refine ⟨?_,flux_hasDerivAt_of_residual l (k : ℂ) _ _ _ r hUD hres⟩
  change HasDerivAt (moment (kernel k y) (angularPolynomial p)) _ r
  rw [← derivative_eq_flux _ r (ne_of_gt ((norm_nonneg y).trans_lt hr))]
  exact hU

def radialState (k : ℝ) (y : Space) (p : Poly) : ℝ → ℂ :=
  RadialMomentODE.riccati (coefficient k y p)

def radialStateD (k : ℝ) (y : Space) (p : Poly) : ℝ → ℂ :=
  RadialMomentODE.riccatiD (coefficient k y p) (radialFlux (momentD (kernel k y) (angularPolynomial p)))

theorem radialState_hasDerivAt (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : ‖y‖ < r) :
    HasDerivAt (radialState k y p) (radialStateD k y p r) r :=
  RadialMomentODE.riccati_hasDerivAt _ _ r (ne_of_gt ((norm_nonneg y).trans_lt hr))
    (exterior_flux_derivatives k y p l hp hh r hr).1

theorem radialStateD_hasDerivAt (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : ‖y‖ < r) :
    HasDerivAt (radialStateD k y p) (radialCoefficient l (k : ℂ) r*radialState k y p r) r :=
  RadialMomentODE.riccatiD_hasDerivAt l (k : ℂ) _ _ r (ne_of_gt ((norm_nonneg y).trans_lt hr))
    (exterior_flux_derivatives k y p l hp hh r hr).1
    (exterior_flux_derivatives k y p l hp hh r hr).2

theorem outgoing_coefficient (k : ℝ) (hk : 0 < k) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    ∃ a : ℂ,(∀ r,‖y‖ < r → (r : ℂ)*coefficient k y p r=a*outgoing l (k : ℂ) r) ∧
      amplitude k y p=a*(-Complex.I)^(l+1) := by
  exact RadialBoundarySelection.ode_outgoing_selection l k hk ‖y‖ (norm_nonneg _)
    (radialState k y p) (radialStateD k y p)
    (fun r hr => radialState_hasDerivAt k y p l hp hh r hr)
    (fun r hr => radialStateD_hasDerivAt k y p l hp hh r hr)
    (amplitude k y p) (coefficient_scaled_limit k y p)

end OQ14.ScalarGreenExterior

#print axioms OQ14.ScalarGreenExterior.scaled_moment_integral
#print axioms OQ14.ScalarGreenExterior.coefficient_scaled_limit
#print axioms OQ14.ScalarGreenExterior.exterior_flux_derivatives
#print axioms OQ14.ScalarGreenExterior.radialState_hasDerivAt
#print axioms OQ14.ScalarGreenExterior.radialStateD_hasDerivAt
#print axioms OQ14.ScalarGreenExterior.outgoing_coefficient
