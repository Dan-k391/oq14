import VectorReactionTerms

/-! Actual central-inversion parity of smooth solid Maxwell fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SolidWaveParity
open OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis

theorem wave_parity (l : ℕ) (k : ℝ) (p : Poly) (hp : p.IsHomogeneous l) (x : Space) :
    SolidScalarHelmholtz.wave l k p (-x)=(-1 : ℂ)^l*SolidScalarHelmholtz.wave l k p x := by
  have he := FischerDecomposition.complexEvaluate_smul p l hp (-1) x
  simp only [neg_one_smul,Complex.ofReal_neg,Complex.ofReal_one] at he
  simp only [SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial,norm_neg,he]
  ring

theorem partial_parity (f : Space → ℂ) (hf : Differentiable ℝ f) (c : ℂ)
    (hp : ∀ x,f (-x)=c*f x) (x : Space) (i : Fin 3) :
    dcoord f (-x) i= -c*dcoord f x i := by
  have he : (fun y => f (-y))=(fun y => c*f y) := funext hp
  have hd := ((hf (-x)).hasFDerivAt.comp x ((hasFDerivAt_id x).neg)).fderiv
  change fderiv ℝ (fun y => f (-y)) x=_ at hd
  rw [he,((hf x).hasFDerivAt.const_mul c).fderiv] at hd
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (Maxwell.basis i)) hd
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.id_apply,map_neg,smul_eq_mul] at hv
  dsimp [dcoord]
  linear_combination hv

theorem curl_parity (F : Field) (hf : ∀ j,Differentiable ℝ (fun x => F x j)) (c : ℂ)
    (hp : ∀ x j,F (-x) j=c*F x j) (x : Space) (i : Fin 3) :
    curl F (-x) i= -c*curl F x i := by
  have hd (a b : Fin 3) := partial_parity (fun y => F y b) (hf b) c (fun y => hp y b) x a
  fin_cases i <;> simp [curl,pd,hd] <;> ring

theorem toroidal_parity (l : ℕ) (k : ℝ) (p : Poly) (hp : p.IsHomogeneous l)
    (x : Space) (i : Fin 3) :
    DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) (-x) i=
      (-1 : ℂ)^l*DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) x i := by
  have h := curl_parity (DebyeCalculus.radialVector (SolidScalarHelmholtz.wave l k p))
    (fun j y => (DebyeCalculus.radialVector_smooth _ y
      (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt j).differentiableAt (by simp))
    (-(-1 : ℂ)^l) (by
      intro y j
      simp only [DebyeCalculus.radialVector,PiLp.neg_apply,Complex.ofReal_neg,wave_parity l k p hp]
      ring) x i
  simpa only [neg_neg] using h

theorem electric_parity (l : ℕ) (k : ℝ) (p : Poly) (hp : p.IsHomogeneous l)
    (x : Space) (i : Fin 3) :
    DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) (-x) i=
      (-1 : ℂ)^(l+1)*DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i := by
  have h := curl_parity (DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p))
    (fun j y => (DebyeCalculus.toroidal_smooth _ y
      (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt j).differentiableAt (by simp))
    ((-1 : ℂ)^l) (toroidal_parity l k p hp) x i
  simpa only [pow_succ,mul_neg,mul_one] using h

theorem component_parity (tm : Bool) (a : SphereHarmonicHilbert.TotalIndex) (x : Space) (i : Fin 3) :
    VectorReactionTerms.component tm a i (-x)=
      (-1 : ℂ)^(a.1+if tm then 1 else 0)*VectorReactionTerms.component tm a i x := by
  cases tm
  · exact (by simpa only [VectorReactionTerms.component,Bool.false_eq_true,if_false,Nat.add_zero] using
      toroidal_parity a.1 1 (representative a.1 a.2) (representative_homogeneous a.1 a.2) x i)
  · exact electric_parity a.1 1 (representative a.1 a.2) (representative_homogeneous a.1 a.2) x i

end OQ14.SolidWaveParity

#print axioms OQ14.SolidWaveParity.wave_parity
#print axioms OQ14.SolidWaveParity.partial_parity
#print axioms OQ14.SolidWaveParity.curl_parity
#print axioms OQ14.SolidWaveParity.toroidal_parity
#print axioms OQ14.SolidWaveParity.electric_parity
#print axioms OQ14.SolidWaveParity.component_parity
