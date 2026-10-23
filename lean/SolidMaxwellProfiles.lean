import SourceRadiationFrequency
import SolidScalarHelmholtz
import DebyeMaxwell

/-! Globally smooth regular Maxwell waves and their actual Riccati profiles. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SolidMaxwellProfiles
open Complex Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.DebyeRadialTrace
  OQ14.DebyeCalculus OQ14.HankelRealBasis
open scoped Topology

def radial (l : ℕ) (r : ℝ) : ℂ := SolidScalarHelmholtz.radial l 1 (r^2)
def electric (l : ℕ) (p : Poly) : Field :=
  DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l 1 p)
def magnetic (l : ℕ) (p : Poly) : Field :=
  DebyeMaxwell.tmMagnetic 1 1 (SolidScalarHelmholtz.wave l 1 p)

theorem radial_smooth (l : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (radial l) :=
  (SolidScalarHelmholtz.radial_contDiff l 1).comp (contDiff_id.pow 2)

theorem radial_regular (l : ℕ) (r : ℝ) (hr : r≠0) :
    radial l r=(regular l r : ℂ)/(r : ℂ)^(l+1) := by
  have hrc : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  unfold radial SolidScalarHelmholtz.radial
  simp only [one_pow,one_mul,Complex.ofReal_pow]
  rw [SolidRadialSeries.normalized_away l _ hrc,regular_eq_psi]

theorem radial_derivative (l : ℕ) (r : ℝ) (hr : r≠0) :
    deriv (radial l) r=(regularD l r : ℂ)/(r : ℂ)^(l+1)-
      (l+1 : ℕ)*(regular l r : ℂ)/(r : ℂ)^(l+2) := by
  have he : radial l =ᶠ[𝓝 r] RadialQuotient.profile l (fun t => (regular l t : ℂ)) := by
    filter_upwards [eventually_ne_nhds hr] with t ht
    exact radial_regular l t ht
  rw [he.deriv_eq]
  exact (RadialQuotient.profile_hasDerivAt l (fun t => (regular l t : ℂ))
    (fun t => (regularD l t : ℂ)) r hr (real_basis_hasDerivAt l r hr).1.ofReal_comp).deriv

theorem magnetic_profile (l : ℕ) (p : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    magnetic l p x i= -I*((regular l ‖x‖ : ℂ)/(‖x‖ : ℂ)^(l+1))*angularToroidal p x i := by
  change -I*1*1*toroidal (scalar (radial l) p) x i=_
  rw [toroidal_components _ (radial_smooth l).contDiffOn p x hx i,
    radial_regular l ‖x‖ (norm_ne_zero_iff.mpr hx)]
  ring

theorem electric_profile (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    electric l p x i=
      ((regularD l ‖x‖ : ℂ)/(‖x‖ : ℂ)^l)*dcoord (complexEvaluate p) x i+
      ((l : ℂ)*(l+1)*(regular l ‖x‖ : ℂ)/(‖x‖ : ℂ)^(l+3)-
        (l : ℂ)*(regularD l ‖x‖ : ℂ)/(‖x‖ : ℂ)^(l+2))*(x i : ℂ)*complexEvaluate p x := by
  have hr : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  change curl (toroidal (scalar (radial l) p)) x i=_
  rw [toroidal_curl _ (radial_smooth l).contDiffOn p l hp hh x hx i,
    radial_derivative l ‖x‖ (norm_ne_zero_iff.mpr hx),
    radial_regular l ‖x‖ (norm_ne_zero_iff.mpr hx)]
  simp only [pow_succ,Nat.cast_add,Nat.cast_one]
  generalize he : (‖x‖ : ℂ)^l=z
  have hz : z≠0 := he ▸ pow_ne_zero l hr
  field_simp [hr,hz]
  ring_nf
  field_simp [hr,hz]
  ring

theorem electric_smooth (l : ℕ) (p : Poly) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric l p x i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact ExteriorClassical.curl_smooth _
    (toroidal_smooth _ x (SolidScalarHelmholtz.wave_contDiff l 1 p).contDiffAt) i

theorem magnetic_smooth (l : ℕ) (p : Poly) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic l p x i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_const.mul (toroidal_smooth _ x
    (SolidScalarHelmholtz.wave_contDiff l 1 p).contDiffAt i)

theorem actual_maxwell (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (x : Space) :
    MaxwellAt 1 1 1 (electric l p) (magnetic l p) x := by
  exact DebyeMaxwell.tm_real_maxwell isOpen_univ _
    (fun _ _ => (SolidScalarHelmholtz.wave_contDiff l 1 p).contDiffAt)
    1 1 1 (by norm_num) (fun y _ => SolidScalarHelmholtz.wave_helmholtz l 1 p hp hh y) x (mem_univ x)

end OQ14.SolidMaxwellProfiles

#print axioms OQ14.SolidMaxwellProfiles.radial_smooth
#print axioms OQ14.SolidMaxwellProfiles.radial_regular
#print axioms OQ14.SolidMaxwellProfiles.radial_derivative
#print axioms OQ14.SolidMaxwellProfiles.magnetic_profile
#print axioms OQ14.SolidMaxwellProfiles.electric_profile
#print axioms OQ14.SolidMaxwellProfiles.electric_smooth
#print axioms OQ14.SolidMaxwellProfiles.magnetic_smooth
#print axioms OQ14.SolidMaxwellProfiles.actual_maxwell
