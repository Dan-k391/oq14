import SphereHarmonicBasis
import AnnularMomentEquation
import AnnularMomentClassical

/-! Actual cross-degree harmonic orthogonality from genuine annular moment equations. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SphereHarmonicOrthogonality

open MeasureTheory Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.RadialMoment OQ14.RadialMomentWeights OQ14.SphericalMomentEquation OQ14.ExteriorHelmholtz

open scoped RealInnerProductSpace

def pairing (p q : Poly) : ℂ := moment (complexEvaluate q) (angularPolynomial p) 1

theorem moment_power (p q : Poly) (m : ℕ) (hq : q.IsHomogeneous m) (r : ℝ) :
    moment (complexEvaluate q) (angularPolynomial p) r=(r : ℂ)^m*pairing p q := by
  unfold pairing moment
  simp only [one_smul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro n
  simp only [complexEvaluate,FischerDecomposition.evaluate_smul q m hq,
    Complex.ofReal_mul,Complex.ofReal_pow]
  ring

theorem power_first_derivative (m : ℕ) (C : ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)^m*C) ((m : ℂ)*(r : ℂ)^(m-1)*C) r :=
  (complex_power_hasDerivAt m r).mul_const C

theorem power_second_derivative (m : ℕ) (C : ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => (m : ℂ)*(t : ℂ)^(m-1)*C)
      ((m : ℂ)*((m-1 : ℕ) : ℂ)*(r : ℂ)^(m-2)*C) r := by
  have h := ((complex_power_hasDerivAt (m-1) r).const_mul (m : ℂ)).mul_const C
  simpa only [Nat.sub_sub,mul_assoc] using h

theorem pairing_zero (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) (hlm : l ≠ m) : pairing p q=0 := by
  let U : ℝ → ℂ := fun r => (r : ℂ)^m*pairing p q
  let UD : ℝ → ℂ := fun r => (m : ℂ)*(r : ℂ)^(m-1)*pairing p q
  let UDD : ℝ → ℂ := fun r => (m : ℂ)*((m-1 : ℕ) : ℂ)*(r : ℂ)^(m-2)*pairing p q
  have hU : ∀ r,r ∈ Ioo (0 : ℝ) 2 → HasDerivAt U (UD r) r :=
    fun r _ => power_first_derivative m (pairing p q) r
  have hUD : ∀ r,r ∈ Ioo (0 : ℝ) 2 → HasDerivAt UD (UDD r) r :=
    fun r _ => power_second_derivative m (pairing p q) r
  have hUDDc : ContinuousOn UDD (Ioo (0 : ℝ) 2) :=
    ((continuous_const.mul (Complex.continuous_ofReal.pow (m-2))).mul continuous_const).continuousOn
  have hu := (complexEvaluate_regular q).contDiffOn (s := AnnularMoment.annulus 0 2)
  have heq : ∀ x,x ∈ AnnularMoment.annulus 0 2 → laplacian (complexEvaluate q) x+(0 : ℂ)^2*complexEvaluate q x=0 := by
    intro x _
    rw [complexEvaluate_laplacian,hqH]
    simp [evaluate]
  have hmom : moment (complexEvaluate q) (angularPolynomial p)=U :=
    funext (moment_power p q m hq)
  have hweak : ∀ η : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) 2 →
      (∫ r : ℝ,coefficientA l U r*((deriv (deriv η) r : ℝ) : ℂ)+
        coefficientB l U r*((deriv η r : ℝ) : ℂ)+coefficientC l 0 U r*(η r : ℂ))=0 := by
    intro η hη hc hs
    have h := AnnularMomentEquation.weak_radial_real_test 0 2 (by norm_num) 0
      (complexEvaluate q) hu heq p l hp hpH η hη hc hs
    simpa only [hmom,coefficientA,coefficientB,coefficientC] using h
  have hz := AnnularMomentClassical.residual_of_weak l 0 0 2 (by norm_num)
    U UD UDD hU hUD hUDDc hweak 1 (by norm_num)
  simp only [U,UD,UDD,Complex.ofReal_one,one_pow,mul_one,one_mul,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul,zero_sub] at hz
  have hcoeff : (m : ℂ)*((m-1 : ℕ) : ℂ)+2*m=(m : ℂ)*(m+1) := by
    cases m with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]; ring
  have hprod : ((m : ℂ)*(m+1)-(l : ℂ)*(l+1))*pairing p q=0 := by
    rw [← hcoeff]
    linear_combination hz
  have hne : (m : ℂ)*(m+1)-(l : ℂ)*(l+1) ≠ 0 := by
    rw [show (m : ℂ)*(m+1)-(l : ℂ)*(l+1)=(m-l)*(m+l+1) by ring]
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      exact_mod_cast hlm.symm
    · have hn : ((m+l+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m+l+1 ≠ 0)
      simpa only [Nat.cast_add,Nat.cast_one] using hn
  exact (mul_eq_zero.mp hprod).resolve_left hne

theorem harmonic_integral_zero (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) (hlm : l ≠ m) :
    (∫ n : Sphere,SpherePolynomial.polynomialMap p n*SpherePolynomial.polynomialMap q n ∂angularMeasure)=0 := by
  apply Complex.ofReal_eq_zero.mp
  have hpair : ((∫ n : Sphere,SpherePolynomial.polynomialMap p n*SpherePolynomial.polynomialMap q n
      ∂angularMeasure : ℝ) : ℂ)=pairing p q := by
    rw [← integral_complex_ofReal]
    unfold pairing moment
    simp only [one_smul,angularPolynomial,complexEvaluate,SpherePolynomial.polynomialMap_apply,
      evaluate,Complex.ofReal_mul,mul_comm,AngularPower.angularMeasure]
  rw [hpair,pairing_zero p q l m hp hq hpH hqH hlm]

theorem angular_cross_inner (l m : ℕ) (i : Index l) (j : Index m) (hlm : l ≠ m) :
    ⟪ContinuousMap.toLp 2 angularMeasure ℝ (angular l i),
      ContinuousMap.toLp 2 angularMeasure ℝ (angular m j)⟫=0 := by
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  exact harmonic_integral_zero (representative m j) (representative l i) m l
    (representative_homogeneous m j) (representative_homogeneous l i)
    (representative_harmonic m j) (representative_harmonic l i) hlm.symm

def allVectors (a : Σ l, Index l) : Ambient :=
  ContinuousMap.toLp 2 angularMeasure ℝ (angular a.1 a.2)

theorem allVectors_orthonormal : Orthonormal ℝ allVectors := by
  rw [orthonormal_iff_ite]
  rintro ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l=m
  · subst m
    simpa only [allVectors,Sigma.mk.inj_iff,heq_eq_eq,and_self_left,true_and,eq_self_iff_true] using
      orthonormal_iff_ite.mp (angular_orthonormal l) i j
  · rw [if_neg (fun h => hlm (congrArg Sigma.fst h))]
    exact angular_cross_inner l m i j hlm

end OQ14.SphereHarmonicOrthogonality

#print axioms OQ14.SphereHarmonicOrthogonality.moment_power
#print axioms OQ14.SphereHarmonicOrthogonality.power_first_derivative
#print axioms OQ14.SphereHarmonicOrthogonality.power_second_derivative
#print axioms OQ14.SphereHarmonicOrthogonality.pairing_zero
#print axioms OQ14.SphereHarmonicOrthogonality.harmonic_integral_zero
#print axioms OQ14.SphereHarmonicOrthogonality.angular_cross_inner
#print axioms OQ14.SphereHarmonicOrthogonality.allVectors_orthonormal
