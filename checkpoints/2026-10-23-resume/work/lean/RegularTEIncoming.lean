import ToroidalPlaneWaveMoment
import RiccatiTransmission
import HarmonicRadiationGeometry
import HankelEnergy

/-! Actual incoming/outgoing Hankel parts and electric amplitudes of regular TE waves. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RegularTEIncoming
open Complex Filter Set Maxwell HarmonicPolynomial DebyeRadialTrace ModalAlgebra
open scoped Topology

def radial (l : ℕ) (inward : Bool) (r : ℝ) : ℂ := if inward then xiMinus l r else xi l r
def radialD (l : ℕ) (inward : Bool) (r : ℝ) : ℂ := if inward then xiMinusD l r else xiD l r
def phase (inward : Bool) (r : ℝ) : ℂ := exp ((if inward then I else -I)*(r : ℂ))
def coefficient (l : ℕ) (inward : Bool) : ℂ := (if inward then I else -I)^(l+1)

theorem radial_hasDerivAt (l : ℕ) (inward : Bool) (r : ℝ) (hr : r≠0) :
    HasDerivAt (radial l inward) (radialD l inward r) r := by
  cases inward
  · simpa [radial,radialD,Function.comp_def] using
      (xi_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).scomp r (GreenKernel.complex_radius_hasDerivAt r)
  · simpa [radial,radialD,Function.comp_def] using
      (xiMinus_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).scomp r (GreenKernel.complex_radius_hasDerivAt r)

theorem profile_smooth (l : ℕ) (inward : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l (radial l inward)) (Ioi 0) := by
  cases inward
  · have he : radial l false=ModalDipole.scaledRadial (xi l) 1 := by funext r; simp [radial,ModalDipole.scaledRadial]
    rw [he]
    exact SphericalScalarWaves.radialProfile_smooth l (xi l) (xiD l) 1 one_ne_zero (xi_hasDerivAt l)
  · have he : radial l true=ModalDipole.scaledRadial (xiMinus l) 1 := by funext r; simp [radial,ModalDipole.scaledRadial]
    rw [he]
    exact SphericalScalarWaves.radialProfile_smooth l (xiMinus l) (xiMinusD l) 1 one_ne_zero (xiMinus_hasDerivAt l)

def electric (l : ℕ) (inward : Bool) (p : Poly) : Field :=
  fun x => (1/2 : ℂ) • RiccatiTransmission.teE l (radial l inward) p x

def magnetic (l : ℕ) (inward : Bool) (p : Poly) : Field :=
  fun x => (1/2 : ℂ) • RiccatiTransmission.teH l 1 (radial l inward) p x

theorem electric_ray (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    electric l inward p (r • (n : Space))=(radial l inward r/(2*(r : ℂ))) • angularToroidal p n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hnorm : ‖r • (n : Space)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  have hx : r • (n : Space)≠0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  ext i
  simp only [electric,Pi.smul_apply,RiccatiTransmission.teE,
    RiccatiDebyeTrace.M_components l _ (profile_smooth l inward) p _ hx i,hnorm,
    HarmonicRadiationGeometry.angularToroidal_smul p l hp,smul_eq_mul]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp [hrc,pow_succ]
  ring

theorem regular_ray (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p) (r • (n : Space))=
      (psi l r/(r : ℂ)) • angularToroidal p n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hnorm : ‖r • (n : Space)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  have hx : r • (n : Space)≠0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  ext i
  have ht := ToroidalPlaneWaveMoment.solid_toroidal_component l 1 p (r • (n : Space)) i
  simp only [ofReal_one] at ht
  rw [DebyeMaxwell.teElectric,ht,
    SolidScalarHelmholtz.wave_regular_factor l 1 _ one_ne_zero _ hx,
    ToroidalPlaneWaveMoment.evaluate_toroidal,HarmonicRadiationGeometry.angularToroidal_smul p l hp]
  simp only [hnorm,one_mul,Pi.smul_apply,smul_eq_mul]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp [hrc,pow_succ]
  ring

theorem regular_split (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p) (r • (n : Space))=
      electric l false p (r • (n : Space))+electric l true p (r • (n : Space)) := by
  rw [regular_ray l p hp n r hr,electric_ray l false p hp n r hr,electric_ray l true p hp n r hr]
  ext i
  simp only [psi,radial,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem scaled_radial (l : ℕ) (inward : Bool) (r : ℝ) :
    phase inward r*radial l inward r=coefficient l inward*hankelPoly l (if inward then -I else I) r := by
  have he (a : ℂ) : exp (a*(r : ℂ))*exp (-a*(r : ℂ))=1 := by rw [← exp_add]; simp
  cases inward <;> dsimp [phase,radial,coefficient,xi,xiMinus,p,pMinus]
  · calc
      _ = (-I)^(l+1)*(exp (-I*(r : ℂ))*exp (I*(r : ℂ)))*hankelPoly l I r := by ring
      _ = _ := by rw [show I*(r : ℂ)= -(-I)*(r : ℂ) by ring,he]; ring
  · calc
      _ = I^(l+1)*(exp (I*(r : ℂ))*exp (-I*(r : ℂ)))*hankelPoly l (-I) r := by ring
      _ = _ := by rw [he]; ring

theorem scaled_radial_limit (l : ℕ) (inward : Bool) :
    Tendsto (fun r : ℝ => phase inward r*radial l inward r) atTop (𝓝 (coefficient l inward)) := by
  simp_rw [scaled_radial]
  simpa only [one_mul,mul_one] using
    (RadialRellich.hankelPoly_radial_limit l 1 one_ne_zero (if inward then -I else I)).const_mul (coefficient l inward)

theorem scaled_radialD (l : ℕ) (inward : Bool) (r : ℝ) :
    phase inward r*radialD l inward r=coefficient l inward*
      ((if inward then -I else I)*hankelPoly l (if inward then -I else I) r+
        hankelPolyD l (if inward then -I else I) r) := by
  have he (a : ℂ) : exp (a*(r : ℂ))*exp (-a*(r : ℂ))=1 := by rw [← exp_add]; simp
  cases inward <;> dsimp [phase,radialD,coefficient,xiD,xiMinusD,p,pMinus,pD,pMinusD]
  · calc
      _ = (-I)^(l+1)*(exp (-I*(r : ℂ))*exp (I*(r : ℂ)))*
          (I*hankelPoly l I r+hankelPolyD l I r) := by ring
      _ = _ := by rw [show I*(r : ℂ)= -(-I)*(r : ℂ) by ring,he]; ring
  · calc
      _ = I^(l+1)*(exp (I*(r : ℂ))*exp (-I*(r : ℂ)))*
          (-I*hankelPoly l (-I) r+hankelPolyD l (-I) r) := by ring
      _ = _ := by rw [he]; ring

theorem scaled_radialD_limit (l : ℕ) (inward : Bool) :
    Tendsto (fun r : ℝ => phase inward r*radialD l inward r) atTop
      (𝓝 (coefficient l inward*(if inward then -I else I))) := by
  simp_rw [scaled_radialD]
  simpa only [one_mul,mul_one,add_zero] using
    ((((RadialRellich.hankelPoly_radial_limit l 1 one_ne_zero (if inward then -I else I)).const_mul
      (if inward then -I else I)).add (HankelEnergy.hankelPolyD_tendsto l (if inward then -I else I))).const_mul
        (coefficient l inward))

theorem magnetic_tangent_ray (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    crossProduct (position n) (magnetic l inward p (r • (n : Space)))=
      (I*radialD l inward r/(2*(r : ℂ))) • angularToroidal p n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hnorm : ‖r • (n : Space)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  have hx : r • (n : Space)≠0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  have hd : HasDerivAt (radial l inward) (radialD l inward r) ‖r • (n : Space)‖ :=
    hnorm.symm ▸ radial_hasDerivAt l inward r hr.ne'
  have hN := RiccatiDebyeTrace.N_cross l (radial l inward) (profile_smooth l inward) p hp hh
    (r • (n : Space)) hx (radialD l inward r) hd
  have hp0 : position (r • (n : Space))=(r : ℂ) • position n := by
    ext i
    simp [position,PiLp.smul_apply]
  rw [hp0,hnorm,HarmonicRadiationGeometry.angularToroidal_smul p l hp] at hN
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hNc : (r : ℂ) • crossProduct (position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space)))=
      (-radialD l inward r) • angularToroidal p n := by
    ext i
    calc
      _ = crossProduct ((r : ℂ) • position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space))) i := by
        fin_cases i <;> simp [cross_apply,Pi.smul_apply,smul_eq_mul]
      _ = _ := by
        rw [hN i]
        simp only [Pi.smul_apply,smul_eq_mul]
        field_simp [hrc,pow_ne_zero]
        ring
  have hNc' := congrArg (fun v : Vector => (r : ℂ)⁻¹ • v) hNc
  simp only [smul_smul,inv_mul_cancel₀ hrc,one_smul] at hNc'
  simp only [magnetic,RiccatiTransmission.teH,div_one,map_smul,hNc',smul_smul]
  congr 1
  field_simp
theorem magnetic_tangent_amplitude (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (n : SphereReactionKernel.Sphere) :
    Tendsto (fun r : ℝ => (phase inward r*(r : ℂ)) •
      crossProduct (position n) (magnetic l inward p (r • (n : Space)))) atTop
      (𝓝 ((I*coefficient l inward*(if inward then -I else I)/2) • angularToroidal p n)) := by
  have ht := (((scaled_radialD_limit l inward).const_mul I).div_const (2 : ℂ)).smul_const (angularToroidal p n)
  simp only [← mul_assoc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [magnetic_tangent_ray l inward p hp hh n r hr,smul_smul]
  congr 1
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

theorem electric_amplitude (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (n : SphereReactionKernel.Sphere) :
    Tendsto (fun r : ℝ => (phase inward r*(r : ℂ)) • electric l inward p (r • (n : Space)))
      atTop (𝓝 ((coefficient l inward/2) • angularToroidal p n)) := by
  have ht := ((scaled_radial_limit l inward).div_const (2 : ℂ)).smul_const (angularToroidal p n)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [electric_ray l inward p hp n r hr,smul_smul]
  congr 1
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

end OQ14.RegularTEIncoming
#print axioms OQ14.RegularTEIncoming.radial_hasDerivAt
#print axioms OQ14.RegularTEIncoming.profile_smooth
#print axioms OQ14.RegularTEIncoming.electric_ray
#print axioms OQ14.RegularTEIncoming.regular_ray
#print axioms OQ14.RegularTEIncoming.regular_split
#print axioms OQ14.RegularTEIncoming.scaled_radial
#print axioms OQ14.RegularTEIncoming.scaled_radial_limit
#print axioms OQ14.RegularTEIncoming.scaled_radialD
#print axioms OQ14.RegularTEIncoming.scaled_radialD_limit
#print axioms OQ14.RegularTEIncoming.magnetic_tangent_ray
#print axioms OQ14.RegularTEIncoming.magnetic_tangent_amplitude
#print axioms OQ14.RegularTEIncoming.electric_amplitude
