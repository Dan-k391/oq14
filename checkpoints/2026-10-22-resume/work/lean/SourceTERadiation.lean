import SourceRadiation
import HarmonicRadiationFactors

/-! Actual all-degree spatial outgoing radiation of the dual TE source field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.SourceTERadiation
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.DebyeRadialTrace OQ14.ModalAlgebra OQ14.SourceRadiation
open scoped Topology

def radiationDefect (d : Data) (p : Poly) (x : Space) : Vector :=
  (Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ)) •
    (SourceGeneralMaxwell.teMagnetic d p x-
      ((‖x‖ : ℂ)⁻¹) • ModalInterface.tangent x (SourceGeneralMaxwell.teElectric d p x))

theorem magnetic_tangent (d : Data) (p : Poly) (x : Space) :
    ModalInterface.tangent x (SourceUnclippedMaxwell.magnetic d p x)=
      (-I*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+1)) • HarmonicRadiationFactors.poloidal p x := by
  ext i
  fin_cases i <;> simp [ModalInterface.tangent,SourceUnclippedMaxwell.magnetic,
    cross_apply,HarmonicRadiationFactors.poloidal,position] <;> ring

theorem scaled_hankel (l : ℕ) (r : ℝ) :
    Complex.exp (-I*(r : ℂ))*xi l r=phase l*p l r := by
  have he : Complex.exp (-I*(r : ℂ))*Complex.exp (I*(r : ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  simp only [xi,phase]
  calc
    _ = (-I)^(l+1)*(Complex.exp (-I*(r : ℂ))*Complex.exp (I*(r : ℂ)))*p l r := by ring
    _ = _ := by rw [he];ring

theorem radiationDefect_exterior (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (x : Space) (hx : d.X<‖x‖) :
    radiationDefect d P x=
      (-amplitude d*phase d.l*pD d.l ‖x‖) •
        (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P x)-
      (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ))) •
        (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x) := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  have hσ : inverseSigma d ‖x‖=1 := by
    simp only [inverseSigma,SourceRadialSystem.extend,
      if_neg (not_le.mpr ((RadialStack.chain_ordered d.chain).trans_lt hx)),if_neg (not_le.mpr hx)]
  calc
    _ = (-(amplitude d*(Complex.exp (-I*(‖x‖ : ℂ))*(xiD d.l ‖x‖-I*xi d.l ‖x‖)))/
          (‖x‖ : ℂ)^(d.l+1)) • HarmonicRadiationFactors.poloidal P x-
        (amplitude d*((d.l : ℂ)*(d.l+1))*(Complex.exp (-I*(‖x‖ : ℂ))*xi d.l ‖x‖)/
          (‖x‖ : ℂ)^(d.l+2)) • HarmonicRadiationFactors.radial P x := by
      rw [radiationDefect,SourceGeneralMaxwell.teElectric,magnetic_tangent]
      ext i
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,SourceGeneralMaxwell.teMagnetic,
        SourceUnclippedMaxwell.electric,hs,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
        RadialStack.outgoing,hσ,one_mul,HarmonicRadiationFactors.poloidal_formula P d.l hp,
        HarmonicRadiationFactors.radial,pow_succ]
      generalize he : (‖x‖ : ℂ)^d.l=z
      have hz : z≠0 := he ▸ pow_ne_zero d.l hr0
      field_simp [hr0,hz]
      ring_nf
      field_simp [hr0,hz]
      ring
    _ = _ := by
      rw [SourceRadiation.hankel_difference,scaled_hankel]
      ext i
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,pow_succ]
      generalize he : (‖x‖ : ℂ)^d.l=z
      have hz : z≠0 := he ▸ pow_ne_zero d.l hr0
      field_simp [hr0,hz]
      ring_nf

theorem radiationDefect_limit (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => radiationDefect d P (γ t)) atTop (𝓝 0) := by
  obtain ⟨M,hM,hbound⟩ := HarmonicRadiationFactors.poloidal_bound P d.l hp
  obtain ⟨N,hN,hnorm⟩ := HarmonicRadiationFactors.radial_bound P d.l hp
  have hpd : Tendsto (fun r : ℝ => pD d.l r) atTop (𝓝 0) := HankelEnergy.hankelPolyD_tendsto d.l I
  have hp0 : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  have hpr : Tendsto (fun r : ℝ => p d.l r/(r : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hp0.mul HankelEnergy.inverse_real_tendsto
  have hl1 : Tendsto (fun t => ‖-amplitude d*phase d.l*pD d.l ‖γ t‖‖*M) atTop (𝓝 0) := by
    simpa only [mul_zero,norm_zero,zero_mul] using
      (((hpd.comp hγ).const_mul (-amplitude d*phase d.l)).norm).mul_const M
  have hl2 : Tendsto (fun t =>
      ‖amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖γ t‖/(‖γ t‖ : ℂ))‖*N) atTop (𝓝 0) := by
    simpa only [mul_zero,norm_zero,zero_mul] using
      (((hpr.comp hγ).const_mul (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1)))).norm).mul_const N
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => norm_nonneg _)) _
    (by simpa only [add_zero] using hl1.add hl2)
  filter_upwards [hγ.eventually (eventually_gt_atTop d.X)] with t ht
  have hn : γ t≠0 := norm_pos_iff.mp ((d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans ht)
  rw [radiationDefect_exterior d P hp (γ t) ht]
  exact (norm_sub_le _ _).trans (add_le_add
    (by rw [norm_smul];exact mul_le_mul_of_nonneg_left (hbound (γ t) hn) (norm_nonneg _))
    (by rw [norm_smul];exact mul_le_mul_of_nonneg_left (hnorm (γ t) hn) (norm_nonneg _)))

end OQ14.SourceTERadiation

#print axioms OQ14.SourceTERadiation.magnetic_tangent
#print axioms OQ14.SourceTERadiation.scaled_hankel
#print axioms OQ14.SourceTERadiation.radiationDefect_exterior
#print axioms OQ14.SourceTERadiation.radiationDefect_limit
