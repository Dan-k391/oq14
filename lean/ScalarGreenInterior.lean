import ScalarGreenOrigin
import ScalarGreenExterior
import RadialOriginSelection

/-! Actual regular selection of the interior Green spherical moments. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.ScalarGreenInterior

open MeasureTheory Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.RadialMoment
  OQ14.SphericalMomentEquation OQ14.ScalarGreenMoment OQ14.ScalarGreenExterior
  OQ14.ScalarGreenOrigin OQ14.RadialMomentWeights OQ14.RadialMomentClassical OQ14.RadialRellich
open scoped Topology

theorem radialStateD_formula (k r : ℝ) (y : Space) (p : Poly) :
    radialStateD k y p r=coefficient k y p r+(r : ℂ)*momentD (kernel k y) (angularPolynomial p) r := by
  unfold radialStateD OQ14.RadialMomentODE.riccatiD radialFlux
  by_cases hr : (r : ℂ)=0
  · simp only [hr,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul,div_zero,add_zero]
  · field_simp [hr]
    ring

theorem radialState_continuousAt_zero (k : ℝ) (y : Space) (hy : y ≠ 0) (p : Poly) :
    ContinuousAt (radialState k y p) 0 :=
  Complex.continuous_ofReal.continuousAt.mul (coefficient_continuousAt_zero k y hy p)

theorem radialStateD_continuousAt_zero (k : ℝ) (y : Space) (hy : y ≠ 0) (p : Poly) :
    ContinuousAt (radialStateD k y p) 0 := by
  simp_rw [show radialStateD k y p=(fun r => coefficient k y p r+(r : ℂ)*
      momentD (kernel k y) (angularPolynomial p) r) from funext (fun r => radialStateD_formula k r y p)]
  exact (coefficient_continuousAt_zero k y hy p).add
    (Complex.continuous_ofReal.continuousAt.mul (coefficientD_continuousAt_zero k y hy p))

theorem radialState_zero (k : ℝ) (y : Space) (p : Poly) : radialState k y p 0=0 := by
  simp only [radialState,OQ14.RadialMomentODE.riccati,Complex.ofReal_zero,zero_mul]

theorem interior_flux_derivatives (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : r ∈ Ioo 0 ‖y‖) :
    HasDerivAt (coefficient k y p)
      (radialFlux (momentD (kernel k y) (angularPolynomial p)) r/(r : ℂ)^2) r ∧
    HasDerivAt (radialFlux (momentD (kernel k y) (angularPolynomial p)))
      (((l : ℂ)*(l+1)-(k : ℂ)^2*(r : ℂ)^2)*coefficient k y p r) r := by
  have hy : ‖y‖ ∉ Ioo 0 ‖y‖ := fun h => (lt_irrefl ‖y‖) h.2
  have hu := kernel_annular_smooth k y 0 ‖y‖ hy
  have hU := AnnularMoment.moment_hasDerivAt 0 ‖y‖ r (by norm_num) hr
    (kernel k y) hu (angularPolynomial p) (angularPolynomial_continuous p)
  have hUD := AnnularMoment.momentD_hasDerivAt 0 ‖y‖ r (by norm_num) hr
    (kernel k y) hu (angularPolynomial p) (angularPolynomial_continuous p)
  have hres := coefficient_classical_annulus k y p l hp hh 0 ‖y‖ (by norm_num) hy r hr
  refine ⟨?_,flux_hasDerivAt_of_residual l (k : ℂ) _ _ _ r hUD hres⟩
  change HasDerivAt (moment (kernel k y) (angularPolynomial p)) _ r
  rw [← derivative_eq_flux _ r (ne_of_gt hr.1)]
  exact hU

theorem radialState_inner_hasDerivAt (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : r ∈ Ioo 0 ‖y‖) :
    HasDerivAt (radialState k y p) (radialStateD k y p r) r :=
  OQ14.RadialMomentODE.riccati_hasDerivAt _ _ r (ne_of_gt hr.1)
    (interior_flux_derivatives k y p l hp hh r hr).1

theorem radialStateD_inner_hasDerivAt (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (r : ℝ) (hr : r ∈ Ioo 0 ‖y‖) :
    HasDerivAt (radialStateD k y p) (radialCoefficient l (k : ℂ) r*radialState k y p r) r :=
  OQ14.RadialMomentODE.riccatiD_hasDerivAt l (k : ℂ) _ _ r (ne_of_gt hr.1)
    (interior_flux_derivatives k y p l hp hh r hr).1
    (interior_flux_derivatives k y p l hp hh r hr).2

theorem regular_coefficient (k : ℝ) (hk : k ≠ 0) (y : Space) (hy : y ≠ 0) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    ∃ a : ℂ,∀ r ∈ Ioo 0 ‖y‖,(r : ℂ)*coefficient k y p r=
      a*OQ14.RiccatiOriginSeries.origin l ((k : ℂ)*r) := by
  exact RadialOriginSelection.regular_selection l (k : ℂ) (Complex.ofReal_ne_zero.mpr hk)
    ‖y‖ (norm_pos_iff.mpr hy) (radialState k y p) (radialStateD k y p)
    (radialState_continuousAt_zero k y hy p) (radialStateD_continuousAt_zero k y hy p)
    (radialState_zero k y p)
    (fun r hr => radialState_inner_hasDerivAt k y p l hp hh r hr)
    (fun r hr => radialStateD_inner_hasDerivAt k y p l hp hh r hr)

end OQ14.ScalarGreenInterior

#print axioms OQ14.ScalarGreenInterior.radialStateD_formula
#print axioms OQ14.ScalarGreenInterior.radialState_continuousAt_zero
#print axioms OQ14.ScalarGreenInterior.radialStateD_continuousAt_zero
#print axioms OQ14.ScalarGreenInterior.radialState_zero
#print axioms OQ14.ScalarGreenInterior.interior_flux_derivatives
#print axioms OQ14.ScalarGreenInterior.radialState_inner_hasDerivAt
#print axioms OQ14.ScalarGreenInterior.radialStateD_inner_hasDerivAt
#print axioms OQ14.ScalarGreenInterior.regular_coefficient
