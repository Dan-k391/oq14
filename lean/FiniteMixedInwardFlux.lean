import FiniteMixedFlux
import SphereTangentialPower

/-! Literal inward radial Poynting integral of the finite incoming half-fields over the sphere of radius r. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.FiniteMixedInwardFlux
open Complex Filter MeasureTheory OQ14.Maxwell OQ14.SphereVectorPairing
open OQ14.SphereHarmonicBasis OQ14.FiniteMixedFlux OQ14.FiniteMixedTraces OQ14.ComplexTransverseExpansion OQ14.FiniteMixedFields
open scoped Topology

def inwardPower (c : ModeIndex →₀ ℂ) (r : ℝ) : ℝ :=
  -r^2*∫ n : Sphere,FarFieldPower.radialPower (n : Space) (electricPart c true (r • (n : Space)))
    (magneticPart c true (r • (n : Space))) ∂SphereReactionKernel.surface

theorem inwardPower_eq_pairing (c : ModeIndex →₀ ℂ) (r : ℝ) (hr : 0<r) :
    inwardPower c r=(pairing (electricMap c r) (magneticMap c r)).re/2 := by
  have hint := integrand_integrable (electricMap c r) (magneticMap c r)
  have hpt : ∀ n : Sphere, -r^2*FarFieldPower.radialPower (n : Space) (electricPart c true (r • (n : Space)))
      (magneticPart c true (r • (n : Space)))=
      (dot (electricMap c r n) (conjugate (magneticMap c r n))).re/2 := by
    intro n
    rw [SphereTangentialPower.scaled_inward_power (n : Space) (by simp) r,
      electricMap_actual c r hr n,magneticMap_actual c r hr n]
  rw [inwardPower,←integral_const_mul]
  simp_rw [hpt]
  rw [integral_div,pairing_integral]
  congr 1
  exact integral_re hint

theorem inwardPower_limit (c : ModeIndex →₀ ℂ) :
    Tendsto (inwardPower c) atTop
      (𝓝 (2*Real.pi^2*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface)) := by
  have h := ((Complex.continuous_re.tendsto _).comp (pairing_limit_real c)).div_const 2
  have he : (((4*Real.pi^2 : ℝ) : ℂ)*pairing (amplitude c) (amplitude c)).re/2=
      2*Real.pi^2*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface := by
    rw [Complex.re_ofReal_mul,pairing_self]
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  exact (inwardPower_eq_pairing c r hr).symm

theorem inwardPower_limit_pos (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    0<2*Real.pi^2*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface :=
  mul_pos (by positivity) (FiniteVectorAngular.amplitude_energy_positive c hc)

end OQ14.FiniteMixedInwardFlux
#print axioms OQ14.FiniteMixedInwardFlux.inwardPower_eq_pairing
#print axioms OQ14.FiniteMixedInwardFlux.inwardPower_limit
#print axioms OQ14.FiniteMixedInwardFlux.inwardPower_limit_pos
