import SourceTERadiation

/-! Actual electric and magnetic outgoing amplitudes of the same layered source state. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceFarAmplitude
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
open OQ14.SourceRadiation OQ14.ModalAlgebra
open scoped Topology

def electricWeighted (d : Data) (p : Poly) (x : Space) : Vector :=
  (Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ)) • SourceUnclippedMaxwell.electric d p x
def magneticWeighted (d : Data) (p : Poly) (x : Space) : Vector :=
  (Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ)) • SourceUnclippedMaxwell.magnetic d p x

theorem electric_exterior (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (x : Space) (hx : d.X<‖x‖) :
    electricWeighted d P x=
      (amplitude d*phase d.l*(I*p d.l ‖x‖+pD d.l ‖x‖)) •
        (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P x)+
      (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ))) •
        (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x) := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  have hσ : inverseSigma d ‖x‖=1 := by
    simp only [inverseSigma,SourceRadialSystem.extend,
      if_neg (not_le.mpr ((RadialStack.chain_ordered d.chain).trans_lt hx)),if_neg (not_le.mpr hx)]
  have hD : Complex.exp (-I*(‖x‖ : ℂ))*xiD d.l ‖x‖=
      phase d.l*(I*p d.l ‖x‖+pD d.l ‖x‖) := by
    have h := SourceRadiation.hankel_difference d.l ‖x‖
    have h0 := SourceTERadiation.scaled_hankel d.l ‖x‖
    linear_combination h+I*h0
  calc
    _ = (amplitude d*(Complex.exp (-I*(‖x‖ : ℂ))*xiD d.l ‖x‖)) •
          (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P x)+
        (amplitude d*((d.l : ℂ)*(d.l+1))*
          ((Complex.exp (-I*(‖x‖ : ℂ))*xi d.l ‖x‖)/(‖x‖ : ℂ))) •
          (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x) := by
      ext i
      simp only [electricWeighted,SourceUnclippedMaxwell.electric,hs,Prod.smul_fst,Prod.smul_snd,
        RadialStack.outgoing,hσ,one_mul,Pi.smul_apply,Pi.add_apply,smul_eq_mul,
        HarmonicRadiationFactors.poloidal_formula P d.l hp,HarmonicRadiationFactors.radial,pow_succ]
      generalize he : (‖x‖ : ℂ)^d.l=z
      have hz : z≠0 := he ▸ pow_ne_zero d.l hr0
      field_simp [hr0,hz]
      ring_nf
      field_simp [hr0,hz]
      ring
    _ = _ := by
      rw [hD,SourceTERadiation.scaled_hankel]
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring

theorem magnetic_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    magneticWeighted d P x=
      (-I*amplitude d*phase d.l*p d.l ‖x‖) •
        (((‖x‖ : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P x) := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  calc
    _ = (-I*amplitude d*(Complex.exp (-I*(‖x‖ : ℂ))*xi d.l ‖x‖)) •
          (((‖x‖ : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P x) := by
      ext i
      simp only [magneticWeighted,SourceUnclippedMaxwell.magnetic,hs,Prod.smul_fst,
        RadialStack.outgoing,Pi.smul_apply,smul_eq_mul,pow_succ]
      field_simp [hr0]
      ring
    _ = _ := by rw [SourceTERadiation.scaled_hankel];congr 1;ring

theorem normalized_ray (F : Field) (l : ℕ)
    (hh : ∀ (r : ℝ) (x : Space),F (r • x)=(r : ℂ)^l • F x)
    (n : SpherePolynomial.Sphere) (r : ℝ) (hr : 0<r) :
    (((‖r • (n : Space)‖ : ℂ)^l)⁻¹) • F (r • (n : Space))=F n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have he : ‖r • (n : Space)‖=r := by rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [he,hh,smul_smul,inv_mul_cancel₀ (pow_ne_zero l (Complex.ofReal_ne_zero.mpr hr.ne')),one_smul]

theorem electric_ray (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (n : SpherePolynomial.Sphere) (r : ℝ) (hr : 0<r) (hR : d.X<r) :
    electricWeighted d P (r • (n : Space))=
      (amplitude d*phase d.l*(I*p d.l r+pD d.l r)) • HarmonicRadiationFactors.poloidal P n+
      (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l r/(r : ℂ))) •
        HarmonicRadiationFactors.radial P n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have he : ‖r • (n : Space)‖=r := by rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [electric_exterior d P hp _ (by rwa [he]),
    normalized_ray _ _ (HarmonicRadiationFactors.poloidal_smul P d.l hp) n r hr,
    normalized_ray _ _ (HarmonicRadiationFactors.radial_smul P d.l hp) n r hr,he]

theorem magnetic_ray (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (n : SpherePolynomial.Sphere) (r : ℝ) (hr : 0<r) (hR : d.X<r) :
    magneticWeighted d P (r • (n : Space))=
      (-I*amplitude d*phase d.l*p d.l r) • DebyeRadialTrace.angularToroidal P n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have he : ‖r • (n : Space)‖=r := by rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [magnetic_exterior d P _ (by rwa [he]),
    normalized_ray _ _ (HarmonicRadiationGeometry.angularToroidal_smul P d.l hp) n r hr,he]

theorem electric_ray_limit (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (n : SpherePolynomial.Sphere) :
    Tendsto (fun r : ℝ => electricWeighted d P (r • (n : Space))) atTop
      (𝓝 ((amplitude d*phase d.l*I) • HarmonicRadiationFactors.poloidal P n)) := by
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  have hpd : Tendsto (fun r : ℝ => pD d.l r) atTop (𝓝 0) := HankelEnergy.hankelPolyD_tendsto d.l I
  have hpr : Tendsto (fun r : ℝ => p d.l r/(r : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hpol.mul HankelEnergy.inverse_real_tendsto
  have h1 := (((hpol.const_mul I).add hpd).const_mul (amplitude d*phase d.l)).smul_const
    (HarmonicRadiationFactors.poloidal P n)
  have h2 := (hpr.const_mul (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1)))).smul_const
    (HarmonicRadiationFactors.radial P n)
  have ht := h1.add h2
  simp only [mul_one,add_zero,mul_zero,zero_smul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (max d.X 0)] with r hr
  exact (electric_ray d P hp n r ((le_max_right _ _).trans_lt hr)
    ((le_max_left _ _).trans_lt hr)).symm

theorem magnetic_ray_limit (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (n : SpherePolynomial.Sphere) :
    Tendsto (fun r : ℝ => magneticWeighted d P (r • (n : Space))) atTop
      (𝓝 ((-I*amplitude d*phase d.l) • DebyeRadialTrace.angularToroidal P n)) := by
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  have ht := (hpol.const_mul (-I*amplitude d*phase d.l)).smul_const (DebyeRadialTrace.angularToroidal P n)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (max d.X 0)] with r hr
  exact (magnetic_ray d P hp n r ((le_max_right _ _).trans_lt hr)
    ((le_max_left _ _).trans_lt hr)).symm

end OQ14.SourceFarAmplitude

#print axioms OQ14.SourceFarAmplitude.electric_exterior
#print axioms OQ14.SourceFarAmplitude.magnetic_exterior
#print axioms OQ14.SourceFarAmplitude.normalized_ray
#print axioms OQ14.SourceFarAmplitude.electric_ray
#print axioms OQ14.SourceFarAmplitude.magnetic_ray
#print axioms OQ14.SourceFarAmplitude.electric_ray_limit
#print axioms OQ14.SourceFarAmplitude.magnetic_ray_limit
