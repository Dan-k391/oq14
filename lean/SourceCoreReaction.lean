import SolidMaxwellProfiles

/-! The exact regular difference between the layered source and its actual vacuum source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SourceCoreReaction
open Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.RadialSource OQ14.HankelRealBasis OQ14.ModalAlgebra

theorem vacuum_coefficients (l : ℕ) (R : ℝ) (hR : 0<R) :
    RadialSource.coefficients l [] R R hR=(1,I) := by
  have hw : (regular l R : ℂ)*irregularD l R-(irregular l R : ℂ)*regularD l R=1 := by
    exact_mod_cast real_wronskian l R hR.ne'
  have h0 : xi l R=(regular l R : ℂ)+I*(irregular l R : ℂ) := by
    simpa only [regular,irregular,mul_comm] using (Complex.re_add_im (xi l R)).symm
  have h1 : xiD l R=(regularD l R : ℂ)+I*(irregularD l R : ℂ) := by
    simpa only [regularD,irregularD,mul_comm] using (Complex.re_add_im (xiD l R)).symm
  apply Prod.ext
  · dsimp only [RadialSource.coefficients,RadialStack.traverse,RadialStack.outgoing,
      RadialStack.act,RadialLayer.inverse,fundamental]
    rw [h0,h1]
    push_cast
    linear_combination hw
  · dsimp only [RadialSource.coefficients,RadialStack.traverse,RadialStack.outgoing,
      RadialStack.act,RadialLayer.inverse,fundamental]
    rw [h0,h1]
    push_cast
    linear_combination I*hw

theorem vacuum_gamma (l : ℕ) (R : ℝ) (hR : 0<R) :
    gamma l [] R R hR= -I := by
  rw [gamma,vacuum_coefficients]
  norm_num [Complex.inv_I]

def vacuum (d : Data) : Data := { d with gs:=[], X:=d.R, chain:=RadialStack.Chain.nil d.R }
def multiplier (d : Data) : ℂ := gamma d.l d.gs d.R d.X d.hR+I

theorem vacuum_raw (d : Data) (r : ℝ) :
    raw (vacuum d) r= -I • RadialStack.outgoing d.l r := by
  change RadialGluing.sourceState d.l [] d.R d.R d.hR r= -I • RadialStack.outgoing d.l r
  by_cases hr : r≤d.R
  · rw [RadialGluing.sourceState_core _ _ _ _ _ r hr]
    simp only [vacuum,coreWave,coreWaveD,vacuum_gamma,RadialStack.outgoing,
      Prod.smul_mk,smul_eq_mul]
    apply Prod.ext
    · apply Complex.ext <;> simp [regular,irregular,Complex.mul_re,Complex.mul_im]
    · apply Complex.ext <;> simp [regularD,irregularD,Complex.mul_re,Complex.mul_im]
  · rw [RadialGluing.sourceState_exterior _ (RadialStack.Chain.nil d.R) d.hR r (lt_of_not_ge hr)]
    simp only [vacuum,vacuum_coefficients,Complex.inv_I]

theorem electric_core_difference (d : Data) (p : Poly) (hp : p.IsHomogeneous d.l)
    (hh : formalLaplacian p=0) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    SourceUnclippedMaxwell.electric d p x-SourceUnclippedMaxwell.electric (vacuum d) p x=
      multiplier d • SolidMaxwellProfiles.electric d.l p x := by
  have hs := RadialGluing.sourceState_core d.l d.gs d.R d.X d.hR ‖x‖ hR
  have hv := RadialGluing.sourceState_core d.l [] d.R d.R d.hR ‖x‖ hR
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    SolidMaxwellProfiles.electric_profile d.l p hp hh x hx i,
    SourceUnclippedMaxwell.electric,raw,vacuum,hs,hv,
    inverseSigma,SourceRadialSystem.extend,if_pos hR,
    coreWave,coreWaveD,vacuum_gamma,multiplier]
  ring

theorem magnetic_core_difference (d : Data) (p : Poly) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    SourceUnclippedMaxwell.magnetic d p x-SourceUnclippedMaxwell.magnetic (vacuum d) p x=
      multiplier d • SolidMaxwellProfiles.magnetic d.l p x := by
  have hs := RadialGluing.sourceState_core d.l d.gs d.R d.X d.hR ‖x‖ hR
  have hv := RadialGluing.sourceState_core d.l [] d.R d.R d.hR ‖x‖ hR
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    SolidMaxwellProfiles.magnetic_profile d.l p x hx i,
    SourceUnclippedMaxwell.magnetic,raw,vacuum,hs,hv,coreWave,vacuum_gamma,multiplier]
  ring

theorem te_electric_core_difference (d : Data) (p : Poly) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    SourceGeneralMaxwell.teElectric d p x-SourceGeneralMaxwell.teElectric (vacuum d) p x=
      multiplier d • SolidMaxwellProfiles.magnetic d.l p x :=
  magnetic_core_difference d p x hx hR

theorem te_magnetic_core_difference (d : Data) (p : Poly) (hp : p.IsHomogeneous d.l)
    (hh : formalLaplacian p=0) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    SourceGeneralMaxwell.teMagnetic d p x-SourceGeneralMaxwell.teMagnetic (vacuum d) p x=
      -multiplier d • SolidMaxwellProfiles.electric d.l p x := by
  have he := electric_core_difference d p hp hh x hx hR
  ext i
  have hi := congrFun he i
  simp only [SourceGeneralMaxwell.teMagnetic,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hi ⊢
  linear_combination -hi

end OQ14.SourceCoreReaction

#print axioms OQ14.SourceCoreReaction.vacuum_coefficients
#print axioms OQ14.SourceCoreReaction.vacuum_gamma
#print axioms OQ14.SourceCoreReaction.vacuum_raw
#print axioms OQ14.SourceCoreReaction.electric_core_difference
#print axioms OQ14.SourceCoreReaction.magnetic_core_difference
#print axioms OQ14.SourceCoreReaction.te_electric_core_difference
#print axioms OQ14.SourceCoreReaction.te_magnetic_core_difference
