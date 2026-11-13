import Packet07SelectedRadiation
import Packet07AngularTranslation

/-! A globally smooth ambient extension of the phase-modulated actual input. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07SmoothAngular
open OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
  OQ14.AngularHarmonicEnergy OQ14.ComplexTransverseExpansion
open scoped BigOperators InnerProductSpace
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

def modePolynomial (m : ModeIndex) (i : Fin 3) : Poly :=
  match m with
  | Sum.inl a => tangential (representative (a.1+1) a.2) (a.1+1) i
  | Sum.inr a => toroidal (representative (a.1+1) a.2) i

def modeDegree (m : ModeIndex) : ℕ :=
  match m with
  | Sum.inl a => a.1
  | Sum.inr a => a.1

def extension (k : ℝ) (a : Space) (c : Input) (i : Fin 3) (x : Space) : ℂ :=
  Complex.exp (((k * ⟪x, a⟫_ℝ : ℝ) : ℂ) * Complex.I) *
    ∑ m ∈ c.support, c m * (normalizer (modeDegree m) : ℂ) * complexEvaluate (modePolynomial m i) x

theorem extension_smooth (k : ℝ) (a : Space) (c : Input) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (extension k a c i) := by
  unfold extension
  apply ContDiff.mul
  · apply Complex.contDiff_exp.comp
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
      ((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space => x)).inner ℝ contDiff_const))).mul contDiff_const)
  · apply ContDiff.sum
    intro m hm
    exact contDiff_const.mul (complexEvaluate_regular (modePolynomial m i))

theorem extension_on_sphere (k : ℝ) (a : Space) (c : Input) (i : Fin 3) (n : Sphere) :
    extension k a c i n = Packet07AngularTranslation.translatedAmplitude k a
      (FiniteVectorAngular.amplitude c) n i := by
  unfold extension
  change _ = SphereReactionKernel.wave k a n * (FiniteVectorAngular.amplitude c n i)
  rw [show SphereReactionKernel.wave k a n = Complex.exp (((k * ⟪(n : Space), a⟫_ℝ : ℝ) : ℂ) * Complex.I) by rfl]
  congr 1
  simp only [FiniteVectorAngular.amplitude, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have hp (s : Finset ModeIndex) (F : ModeIndex → ComplexVectorSphere.Vector) :
      (∑ m ∈ s, F m) i = ∑ m ∈ s, F m i :=
    map_sum (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ) F s
  rw [hp]
  simp only [PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  cases m with
  | inl b => simp [FiniteVectorAngular.angular, FiniteVectorAngular.realAngular,
      VectorHarmonicNormalization.restriction, SpherePolynomial.polynomialMap_apply,
      modeDegree, modePolynomial, complexEvaluate, evaluate, ComplexVectorSphere.embed_apply,
      PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  | inr b => simp [FiniteVectorAngular.angular, FiniteVectorAngular.realAngular,
      VectorHarmonicNormalization.restriction, SpherePolynomial.polynomialMap_apply,
      modeDegree, modePolynomial, complexEvaluate, evaluate, ComplexVectorSphere.embed_apply,
      PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]

end OQ14.Packet07SmoothAngular
#print axioms OQ14.Packet07SmoothAngular.extension_smooth
#print axioms OQ14.Packet07SmoothAngular.extension_on_sphere
