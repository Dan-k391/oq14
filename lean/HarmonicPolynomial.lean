import ExteriorHelmholtz
import SpherePolynomial
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Actual harmonic polynomial calculus in Euclidean three-space -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.HarmonicPolynomial
open MeasureTheory OQ14.Maxwell
open MvPolynomial
open scoped InnerProductSpace
abbrev Poly := MvPolynomial (Fin 3) ℝ

def radiusSq : Poly := ∑ i : Fin 3, X i ^ 2

def formalLaplacian : Poly →ₗ[ℝ] Poly :=
  ∑ i : Fin 3, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

theorem formalLaplacian_apply (p : Poly) :
    formalLaplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := rfl

theorem pderiv_radiusSq (i : Fin 3) : pderiv i radiusSq = 2 * X i := by
  fin_cases i <;> simp [radiusSq, Fin.sum_univ_three, pderiv_pow]

theorem second_radiusSq_mul (p : Poly) (i : Fin 3) :
    pderiv i (pderiv i (radiusSq*p)) =
      2*p + 4*X i*pderiv i p + radiusSq*pderiv i (pderiv i p) := by
  have h2 : pderiv i (2 : Poly) = 0 := (pderiv i).map_natCast 2
  simp only [pderiv_mul, pderiv_radiusSq, map_add, h2,
    pderiv_X_self, Derivation.map_natCast, mul_one, zero_mul, zero_add]
  ring

theorem formalLaplacian_radiusSq_mul (p : Poly) :
    formalLaplacian (radiusSq*p) =
      6*p + 4*(∑ i : Fin 3, X i*pderiv i p) + radiusSq*formalLaplacian p := by
  simp only [formalLaplacian_apply, second_radiusSq_mul, Fin.sum_univ_three]
  ring

theorem radiusSq_homogeneous : radiusSq.IsHomogeneous 2 := by
  exact IsHomogeneous.sum Finset.univ _ 2 (fun i _ => isHomogeneous_X_pow i 2)

theorem formalLaplacian_homogeneous (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n) :
    (formalLaplacian p).IsHomogeneous (n-2) := by
  rw [formalLaplacian_apply]
  apply IsHomogeneous.sum Finset.univ _ _
  intro i _
  simpa only [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

theorem homogeneous_radiusSq_mul (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n) :
    formalLaplacian (radiusSq*p) =
      C (4*(n : ℝ)+6)*p + radiusSq*formalLaplacian p := by
  rw [formalLaplacian_radiusSq_mul, hp.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, map_add, map_mul, map_ofNat, map_natCast]
  ring

def radialCoefficient (l j : ℕ) : ℝ := 2*(j : ℝ)*(2*(l : ℝ)+2*(j : ℝ)+1)

theorem radialCoefficient_positive (l j : ℕ) : 0 < radialCoefficient l (j+1) := by
  unfold radialCoefficient
  positivity

theorem radiusSq_pow_homogeneous (h : Poly) (l j : ℕ) (hh : h.IsHomogeneous l) :
    (radiusSq^j*h).IsHomogeneous (l+2*j) := by
  simpa only [Nat.add_comm] using (radiusSq_homogeneous.pow j).mul hh

theorem formalLaplacian_radiusSq_pow (h : Poly) (l : ℕ) (hh : h.IsHomogeneous l)
    (harm : formalLaplacian h = 0) (j : ℕ) :
    formalLaplacian (radiusSq^(j+1)*h) =
      C (radialCoefficient l (j+1)) * (radiusSq^j*h) := by
  induction j with
  | zero =>
    rw [pow_one, homogeneous_radiusSq_mul h l hh, harm]
    simp only [mul_zero, add_zero, pow_zero, one_mul, radialCoefficient, Nat.cast_one]
    congr 1
    ring
  | succ j ih =>
    have he : radiusSq^(j+1+1)*h = radiusSq*(radiusSq^(j+1)*h) := by ring
    rw [he, homogeneous_radiusSq_mul _ (l+2*(j+1))
      (radiusSq_pow_homogeneous h l (j+1) hh), ih]
    simp only [radialCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, map_add, map_mul, map_ofNat, C_1]
    ring

def evaluate (p : Poly) (x : Space) : ℝ := MvPolynomial.eval (fun i => x i) p

def complexEvaluate (p : Poly) (x : Space) : ℂ := (evaluate p x : ℂ)

theorem evaluate_C (r : ℝ) : evaluate (C r) = fun _ => r := by
  funext x
  simp [evaluate]

theorem evaluate_X (i : Fin 3) : evaluate (X i) = fun x => x i := by
  funext x
  simp [evaluate]

theorem evaluate_add (p q : Poly) : evaluate (p+q) = evaluate p + evaluate q := by
  funext x
  simp [evaluate]

theorem evaluate_mul (p q : Poly) : evaluate (p*q) = evaluate p * evaluate q := by
  funext x
  simp [evaluate]

theorem evaluate_regular (p : Poly) : ContDiff ℝ (⊤ : ℕ∞) (evaluate p) := by
  induction p using MvPolynomial.induction_on with
  | C r => rw [evaluate_C]; exact contDiff_const
  | add p q hp hq => rw [evaluate_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [evaluate_mul, evaluate_X]
    exact hp.mul (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

theorem evaluate_partial_X (i j : Fin 3) (x : Space) :
    fderiv ℝ (evaluate (X j)) x (basis i) = if i=j then 1 else 0 := by
  rw [evaluate_X]
  change fderiv ℝ (EuclideanSpace.proj j : Space →L[ℝ] ℝ) x (basis i) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basis, EuclideanSpace.single_apply, eq_comm]

theorem evaluate_partial (p : Poly) (x : Space) (i : Fin 3) :
    fderiv ℝ (evaluate p) x (basis i) = evaluate (pderiv i p) x := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [evaluate_C, pderiv_C, evaluate]
  | add p q hp hq =>
    have hdP := (evaluate_regular p).differentiable (by simp) x
    have hdQ := (evaluate_regular q).differentiable (by simp) x
    rw [evaluate_add]
    change fderiv ℝ (fun y => evaluate p y + evaluate q y) x (basis i) = _
    rw [fderiv_add hdP hdQ]
    simp only [ContinuousLinearMap.add_apply, hp, hq, map_add, evaluate_add, Pi.add_apply]
  | mul_X p j hp =>
    have hdP := (evaluate_regular p).differentiable (by simp) x
    have hdX := (evaluate_regular (X j)).differentiable (by simp) x
    rw [evaluate_mul]
    change fderiv ℝ (fun y => evaluate p y * evaluate (X j) y) x (basis i) = _
    rw [fderiv_mul hdP hdX]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hp, evaluate_partial_X, pderiv_mul, evaluate_add, Pi.add_apply, evaluate_mul, Pi.mul_apply]
    by_cases hij : i=j
    · subst j
      simp [pderiv_X_self, evaluate_C, evaluate, mul_comm, add_comm]
    · simp [pderiv_X_of_ne (Ne.symm hij), evaluate_C, hij, evaluate, mul_comm]

theorem complexEvaluate_regular (p : Poly) : ContDiff ℝ (⊤ : ℕ∞) (complexEvaluate p) :=
  Complex.ofRealCLM.contDiff.comp (evaluate_regular p)

theorem complexEvaluate_partial (p : Poly) (x : Space) (i : Fin 3) :
    dcoord (complexEvaluate p) x i = (evaluate (pderiv i p) x : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((evaluate_regular p).differentiable (by simp) x).hasFDerivAt
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv
  simpa only [complexEvaluate, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    evaluate_partial] using hv


theorem complexEvaluate_laplacian (p : Poly) (x : Space) :
    ExteriorHelmholtz.laplacian (complexEvaluate p) x =
      (evaluate (formalLaplacian p) x : ℂ) := by
  unfold ExteriorHelmholtz.laplacian
  calc
    _ = ∑ i : Fin 3, (evaluate (pderiv i (pderiv i p)) x : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (fun y => dcoord (complexEvaluate p) y i) =
        complexEvaluate (pderiv i p) from funext (fun y => complexEvaluate_partial p y i)]
      exact complexEvaluate_partial (pderiv i p) x i
    _ = _ := by simp [formalLaplacian_apply, evaluate, map_sum]
theorem complexEvaluate_euler (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n) (x : Space) :
    (∑ i : Fin 3, (x i : ℂ) * dcoord (complexEvaluate p) x i) =
      (n : ℂ) * complexEvaluate p x := by
  have h := congrArg (MvPolynomial.eval (fun i => x i)) hp.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, nsmul_eq_mul] at h
  simp_rw [complexEvaluate_partial]
  simp only [map_natCast] at h
  simpa [evaluate, complexEvaluate] using congrArg Complex.ofReal h
end OQ14.HarmonicPolynomial

#print axioms OQ14.HarmonicPolynomial.formalLaplacian_apply
#print axioms OQ14.HarmonicPolynomial.pderiv_radiusSq
#print axioms OQ14.HarmonicPolynomial.second_radiusSq_mul
#print axioms OQ14.HarmonicPolynomial.formalLaplacian_radiusSq_mul
#print axioms OQ14.HarmonicPolynomial.radiusSq_homogeneous
#print axioms OQ14.HarmonicPolynomial.formalLaplacian_homogeneous
#print axioms OQ14.HarmonicPolynomial.homogeneous_radiusSq_mul
#print axioms OQ14.HarmonicPolynomial.radialCoefficient_positive
#print axioms OQ14.HarmonicPolynomial.radiusSq_pow_homogeneous
#print axioms OQ14.HarmonicPolynomial.formalLaplacian_radiusSq_pow
#print axioms OQ14.HarmonicPolynomial.evaluate_C
#print axioms OQ14.HarmonicPolynomial.evaluate_X
#print axioms OQ14.HarmonicPolynomial.evaluate_add
#print axioms OQ14.HarmonicPolynomial.evaluate_mul
#print axioms OQ14.HarmonicPolynomial.evaluate_regular
#print axioms OQ14.HarmonicPolynomial.evaluate_partial_X
#print axioms OQ14.HarmonicPolynomial.evaluate_partial
#print axioms OQ14.HarmonicPolynomial.complexEvaluate_regular
#print axioms OQ14.HarmonicPolynomial.complexEvaluate_partial
#print axioms OQ14.HarmonicPolynomial.complexEvaluate_laplacian
#print axioms OQ14.HarmonicPolynomial.complexEvaluate_euler
