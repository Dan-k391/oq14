import HarmonicRadiationGeometry

/-! Actual all-degree outgoing spatial radiation of the normalized layered source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceRadiation
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.DebyeRadialTrace OQ14.ModalAlgebra
open scoped Topology

def amplitude (d : Data) : ℂ := (RadialSource.coefficients d.l d.gs d.R d.X d.hR).2⁻¹
def phase (l : ℕ) : ℂ := (-I)^(l+1)

def radiationDefect (d : Data) (p : Poly) (x : Space) : Vector :=
  (Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ)) •
    (SourceUnclippedMaxwell.magnetic d p x-
      ((‖x‖ : ℂ)⁻¹) • ModalInterface.tangent x (SourceUnclippedMaxwell.electric d p x))

theorem electric_tangent (d : Data) (p : Poly) (x : Space) :
    ModalInterface.tangent x (SourceUnclippedMaxwell.electric d p x)=
      (-(raw d ‖x‖).2/(‖x‖ : ℂ)^d.l) • angularToroidal p x := by
  ext i
  fin_cases i <;> simp [ModalInterface.tangent,SourceUnclippedMaxwell.electric,
    cross_apply,angularToroidal] <;> ring

theorem hankel_difference (l : ℕ) (r : ℝ) :
    Complex.exp (-I*(r : ℂ))*(xiD l r-I*xi l r)=phase l*pD l r := by
  have he : Complex.exp (-I*(r : ℂ))*Complex.exp (I*(r : ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  simp only [xiD,xi,phase]
  calc
    _ = (-I)^(l+1)*(Complex.exp (-I*(r : ℂ))*Complex.exp (I*(r : ℂ)))*pD l r := by ring
    _ = _ := by rw [he];ring

theorem radiationDefect_exterior (d : Data) (p : Poly) (x : Space) (hx : d.X<‖x‖) :
    radiationDefect d p x=
      (amplitude d*phase d.l*pD d.l ‖x‖) • (((‖x‖ : ℂ)^d.l)⁻¹ • angularToroidal p x) := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  rw [radiationDefect,electric_tangent]
  ext i
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,SourceUnclippedMaxwell.magnetic,
    hs,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RadialStack.outgoing,smul_smul]
  calc
    _ = (amplitude d*(Complex.exp (-I*(‖x‖ : ℂ))*
        (xiD d.l ‖x‖-I*xi d.l ‖x‖))/(‖x‖ : ℂ)^d.l)*angularToroidal p x i := by
      simp only [pow_succ]
      field_simp [hr0]
      ring
    _ = _ := by rw [hankel_difference];simp only [div_eq_mul_inv];ring

theorem radiationDefect_limit (d : Data) (p : Poly) (hp : p.IsHomogeneous d.l)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => radiationDefect d p (γ t)) atTop (𝓝 0) := by
  obtain ⟨M,hM,hbound⟩ := HarmonicRadiationGeometry.normalized_toroidal_bound p d.l hp
  have hpd : Tendsto (fun r : ℝ => pD d.l r) atTop (𝓝 0) := HankelEnergy.hankelPolyD_tendsto d.l I
  have hl : Tendsto (fun t => ‖amplitude d*phase d.l‖*‖pD d.l ‖γ t‖‖*M) atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero,zero_mul] using
      (((hpd.comp hγ).norm).const_mul ‖amplitude d*phase d.l‖).mul_const M
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => norm_nonneg _)) _ hl
  filter_upwards [hγ.eventually (eventually_gt_atTop d.X)] with t ht
  have hr : 0<‖γ t‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans ht
  rw [radiationDefect_exterior d p (γ t) ht,norm_smul,norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound (γ t) (norm_pos_iff.mp hr)) (by positivity)

end OQ14.SourceRadiation

#print axioms OQ14.SourceRadiation.electric_tangent
#print axioms OQ14.SourceRadiation.hankel_difference
#print axioms OQ14.SourceRadiation.radiationDefect_exterior
#print axioms OQ14.SourceRadiation.radiationDefect_limit
