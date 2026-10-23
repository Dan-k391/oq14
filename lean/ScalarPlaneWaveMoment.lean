import ScalarGreenNormalization
import SolidMaxwellProfiles
import SphereWaveCalculus

/-! Actual plane-wave harmonic moments, with phase and normalization from the Green source jump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarPlaneWaveMoment
open Complex MeasureTheory Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.ScalarGreenMoment OQ14.ScalarGreenExterior OQ14.ScalarGreenJump
  OQ14.SphericalMomentEquation OQ14.SphereWaveCalculus
open scoped Topology RealInnerProductSpace

theorem amplitude_unit_away (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (y : Space) (hy : y≠0) :
    amplitude 1 y p=(-I)^l*SolidScalarHelmholtz.wave l 1 p y := by
  obtain ⟨a,ha,ham⟩ := outgoing_coefficient 1 (by norm_num) y p l hp hh
  let r := ‖y‖+1
  have hr : 0<r := by dsimp [r]; positivity
  have hry : ‖y‖<r := by dsimp [r]; linarith
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hyc : (‖y‖ : ℂ)≠0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hxi : ModalAlgebra.xi l r≠0 := by
    simpa only [RadialStack.traverse,RadialStack.outgoing] using
      RadialStack.outgoing_traverse_nonzero l [] r hr
  have hc := ScalarGreenNormalization.coefficient_formula 1 (by norm_num) y hy p l hp hh r hr hry.ne'
  have ho := ha r hry
  rw [hc,min_eq_right hry.le,max_eq_left hry.le] at ho
  have he : a=I*SolidScalarHelmholtz.wave l 1 p y := by
    apply mul_right_cancel₀ hxi
    rw [SolidScalarHelmholtz.wave_regular_factor l 1 p one_ne_zero y hy]
    simp only [RadialRellich.outgoing,ofReal_one,one_mul] at ho ⊢
    rw [← ho]
    simp only [innerProfile,outerProfile,RadialQuotient.profile,RadialOriginSelection.regular,
      RadialRellich.outgoing,ofReal_one,one_mul,pow_one,
      RiccatiOriginSeries.origin_eq_psi l (‖y‖ : ℂ) hyc,pow_succ]
    field_simp [hrc,hyc]
    ring
  rw [ham,he,pow_succ]
  ring_nf
  simp [I_sq]

theorem amplitude_moment (p : Poly) (y : Space) :
    amplitude 1 y p=(4*Real.pi : ℂ)⁻¹*moment (angularPolynomial p) (-1) y := by
  unfold amplitude moment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with n
  simp only [SphereReactionKernel.wave,ofReal_one,mul_one,ofReal_neg,
    ofReal_mul,neg_mul,one_mul]
  have he : -(I*(↑(@inner ℝ Space _ (n : Space) y) : ℂ))=
      -((↑(@inner ℝ Space _ (n : Space) y) : ℂ)*I) := by ring
  rw [he]
  ring

theorem moment_continuous (p : Poly) (k : ℝ) : Continuous (moment (angularPolynomial p) k) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (moment_hasFDerivAt _ (angularPolynomial_continuous p)
    ‖SpherePolynomial.polynomialMap p‖ _ k y).continuousAt
  intro n
  simpa only [angularPolynomial,complexEvaluate,evaluate,Complex.norm_real,
    SpherePolynomial.polynomialMap_apply] using (SpherePolynomial.polynomialMap p).norm_coe_le_norm n

theorem negative_unit_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (y : Space) :
    moment (angularPolynomial p) (-1) y=(4*Real.pi : ℂ)*(-I)^l*SolidScalarHelmholtz.wave l 1 p y := by
  have hp0 : (4*Real.pi : ℂ)≠0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have he : moment (angularPolynomial p) (-1)=
      (fun x => (4*Real.pi : ℂ)*(-I)^l*SolidScalarHelmholtz.wave l 1 p x) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Space)) (moment_continuous p (-1))
      (continuous_const.mul (SolidScalarHelmholtz.wave_contDiff l 1 p).continuous)
    intro x hx
    have hx0 : x≠0 := hx
    have h := amplitude_unit_away l p hp hh x hx0
    rw [amplitude_moment] at h
    calc
      _ = (4*Real.pi : ℂ)*((4*Real.pi : ℂ)⁻¹*moment (angularPolynomial p) (-1) x) := by
        rw [← mul_assoc,mul_inv_cancel₀ hp0,one_mul]
      _ = _ := by rw [h];ring
  exact congrFun he y

theorem solid_wave_scale (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (k : ℝ) (y : Space) :
    SolidScalarHelmholtz.wave l 1 p (k • y)=(k : ℂ)^l*SolidScalarHelmholtz.wave l k p y := by
  simp only [SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,ofReal_mul,ofReal_pow,one_pow,one_mul,
    FischerDecomposition.complexEvaluate_smul p l hp]
  ring

theorem negative_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (y : Space) :
    moment (angularPolynomial p) (-k) y=
      (4*Real.pi : ℂ)*(-I)^l*(k : ℂ)^l*SolidScalarHelmholtz.wave l k p y := by
  have he : moment (angularPolynomial p) (-k) y=moment (angularPolynomial p) (-1) (k • y) := by
    unfold moment
    apply integral_congr_ae
    filter_upwards with n
    congr 1
    unfold SphereReactionKernel.wave
    congr 1
    simp only [inner_smul_right,ofReal_neg,ofReal_mul,ofReal_one]
    ring
  rw [he,negative_unit_moment l p hp hh,solid_wave_scale l p hp]
  ring

theorem positive_moment (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (k : ℝ) (y : Space) :
    moment (angularPolynomial p) k y=
      (4*Real.pi : ℂ)*I^l*(k : ℂ)^l*SolidScalarHelmholtz.wave l k p y := by
  have he := negative_moment l p hp hh (-k) y
  simp only [neg_neg,ofReal_neg,SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial,neg_sq] at he ⊢
  rw [he]
  have hpow : (-I)^l*(-(k : ℂ))^l=I^l*(k : ℂ)^l := by
    rw [← mul_pow,← mul_pow]
    congr 1
    ring
  calc
    _ = (4*Real.pi : ℂ)*((-I)^l*(-(k : ℂ))^l)*
        (SolidRadialSeries.F l ((k : ℂ)^2*((‖y‖^2 : ℝ) : ℂ))*complexEvaluate p y) := by ring
    _ = _ := by rw [hpow];ring

end OQ14.ScalarPlaneWaveMoment

#print axioms OQ14.ScalarPlaneWaveMoment.amplitude_unit_away
#print axioms OQ14.ScalarPlaneWaveMoment.amplitude_moment
#print axioms OQ14.ScalarPlaneWaveMoment.moment_continuous
#print axioms OQ14.ScalarPlaneWaveMoment.negative_unit_moment
#print axioms OQ14.ScalarPlaneWaveMoment.solid_wave_scale
#print axioms OQ14.ScalarPlaneWaveMoment.negative_moment
#print axioms OQ14.ScalarPlaneWaveMoment.positive_moment
