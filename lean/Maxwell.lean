import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Coordinate Maxwell calculus on genuine Euclidean three-space

Every partial derivative below is a real Frechet derivative evaluated on
an actual coordinate basis vector. Maxwell equations are equalities between
these differential operators, not axioms attached to an abstract field.
The results here concern classical local fields. They do not yet implement
the weak scattering/interface theory required by the full research target.
-/

noncomputable section
set_option autoImplicit false

namespace OQ14.Maxwell

open Matrix
open scoped ComplexConjugate

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Vector := Fin 3 → ℂ
abbrev Field := Space → Vector

def basis (i : Fin 3) : Space := EuclideanSpace.single i 1

def dcoord (f : Space → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  fderiv ℝ f x (basis i)

def pd (F : Field) (x : Space) (i j : Fin 3) : ℂ :=
  dcoord (fun y => F y j) x i

def curl (F : Field) (x : Space) : Vector :=
  ![pd F x 1 2 - pd F x 2 1,
    pd F x 2 0 - pd F x 0 2,
    pd F x 0 1 - pd F x 1 0]

def divergence (F : Field) (x : Space) : ℂ :=
  pd F x 0 0 + pd F x 1 1 + pd F x 2 2

def dot (v w : Vector) : ℂ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def conjugate (v : Vector) : Vector := fun j => conj (v j)

def crossField (E H : Field) : Field := fun x => crossProduct (E x) (H x)

def conjField (H : Field) : Field := fun x => conjugate (H x)

def energy (v : Vector) : ℝ :=
  Complex.normSq (v 0) + Complex.normSq (v 1) + Complex.normSq (v 2)

/-- The source-free frequency-domain curl equations, with real local
physical coefficients and the exp(-i omega t) convention. -/
def MaxwellAt (ω μ ε : ℝ) (E H : Field) (x : Space) : Prop :=
  curl E x = (fun j => Complex.I * ω * μ * H x j) ∧
  curl H x = (fun j => -Complex.I * ω * ε * E x j)

theorem partial_sub {f g : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    dcoord (fun y => f y - g y) x i = dcoord f x i - dcoord g x i := by
  simp only [dcoord, fderiv_sub hf hg, ContinuousLinearMap.sub_apply]

theorem partial_add {f g : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    dcoord (fun y => f y + g y) x i = dcoord f x i + dcoord g x i := by
  simp only [dcoord, fderiv_add hf hg, ContinuousLinearMap.add_apply]

theorem partial_const_mul {f : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (c : ℂ) (i : Fin 3) :
    dcoord (fun y => c * f y) x i = c * dcoord f x i := by
  simp [dcoord, fderiv_const_mul hf]

theorem partial_mul {f g : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    dcoord (fun y => f y * g y) x i =
      f x * dcoord g x i + g x * dcoord f x i := by
  simp only [dcoord, fderiv_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem differentiableAt_conj {f : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

theorem partial_conj {f : Space → ℂ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    dcoord (fun y => conj (f y)) x i = conj (dcoord f x i) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  unfold dcoord
  change (fderiv ℝ (Complex.conjCLE ∘ f) x) (basis i) =
    Complex.conjCLE ((fderiv ℝ f x) (basis i))
  rw [hd]
  rfl

/-- The actual differential identity div(E cross H) = H dot curl(E)
minus E dot curl(H), derived componentwise from the Frechet product rule. -/
theorem divergence_cross (E H : Field) (x : Space)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x) :
    divergence (crossField E H) x =
      dot (H x) (curl E x) - dot (E x) (curl H x) := by
  have hp (i j : Fin 3) := (hE i).mul (hH j)
  dsimp [divergence, crossField, curl, dot, pd, cross_apply]
  rw [partial_sub (hp 1 2) (hp 2 1),
    partial_sub (hp 2 0) (hp 0 2),
    partial_sub (hp 0 1) (hp 1 0)]
  rw [partial_mul (hE 1) (hH 2), partial_mul (hE 2) (hH 1),
    partial_mul (hE 2) (hH 0), partial_mul (hE 0) (hH 2),
    partial_mul (hE 0) (hH 1), partial_mul (hE 1) (hH 0)]
  ring

theorem curl_conj (H : Field) (x : Space)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x) :
    curl (conjField H) x = conjugate (curl H x) := by
  ext j
  fin_cases j <;>
    simp [curl, conjField, conjugate, pd, partial_conj, hH, map_sub]

theorem curl_add (E H : Field) (x : Space)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x) :
    curl (fun y j => E y j + H y j) x = fun j => curl E x j + curl H x j := by
  ext j
  fin_cases j <;> simp [curl, pd, partial_add, hE, hH] <;> ring

theorem curl_const_mul (E : Field) (x : Space) (c : ℂ)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x) :
    curl (fun y j => c * E y j) x = fun j => c * curl E x j := by
  ext j
  fin_cases j <;> simp [curl, pd, partial_const_mul, hE] <;> ring

theorem maxwell_superposition (ω μ ε : ℝ) (E₁ H₁ E₂ H₂ : Field)
    (a b : ℂ) (x : Space)
    (hE₁ : ∀ j, DifferentiableAt ℝ (fun y => E₁ y j) x)
    (hH₁ : ∀ j, DifferentiableAt ℝ (fun y => H₁ y j) x)
    (hE₂ : ∀ j, DifferentiableAt ℝ (fun y => E₂ y j) x)
    (hH₂ : ∀ j, DifferentiableAt ℝ (fun y => H₂ y j) x)
    (hm₁ : MaxwellAt ω μ ε E₁ H₁ x) (hm₂ : MaxwellAt ω μ ε E₂ H₂ x) :
    MaxwellAt ω μ ε (fun y j => a * E₁ y j + b * E₂ y j)
      (fun y j => a * H₁ y j + b * H₂ y j) x := by
  constructor
  · rw [curl_add _ _ x (fun j => (hE₁ j).const_mul a)
      (fun j => (hE₂ j).const_mul b), curl_const_mul _ _ _ hE₁,
      curl_const_mul _ _ _ hE₂, hm₁.1, hm₂.1]
    ext j
    ring
  · rw [curl_add _ _ x (fun j => (hH₁ j).const_mul a)
      (fun j => (hH₂ j).const_mul b), curl_const_mul _ _ _ hH₁,
      curl_const_mul _ _ _ hH₂, hm₁.2, hm₂.2]
    ext j
    ring

/-- The actual second-order electric Maxwell equation follows from both
first-order equations; no second-order law is assumed. -/
theorem maxwell_curl_curl (ω μ ε : ℝ) (E H : Field)
    (hH : ∀ j, Differentiable ℝ (fun y => H y j))
    (hMax : ∀ x, MaxwellAt ω μ ε E H x) (x : Space) :
    curl (curl E) x = fun j => (ω : ℂ) ^ 2 * μ * ε * E x j := by
  have he : curl E = fun y j => Complex.I * ω * μ * H y j :=
    funext (fun y => (hMax y).1)
  rw [he, curl_const_mul H x (Complex.I * ω * μ) (fun j => hH j x), (hMax x).2]
  ext j
  simp [mul_assoc, ← mul_pow, Complex.I_sq]
  ring_nf
  simp [Complex.I_sq]

theorem dot_conjugate (v : Vector) : dot v (conjugate v) = (energy v : ℂ) := by
  simp [dot, conjugate, energy, Complex.mul_conj, Complex.ofReal_add]

theorem conjugate_dot (v : Vector) : dot (conjugate v) v = (energy v : ℂ) := by
  simpa only [dot, conjugate, mul_comm] using dot_conjugate v

/-- Complex Poynting identity for differentiable actual Maxwell fields.
The right side is purely imaginary for real permittivity/permeability. -/
theorem complex_poynting_identity (ω μ ε : ℝ) (E H : Field) (x : Space)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x)
    (hMax : MaxwellAt ω μ ε E H x) :
    divergence (crossField E (conjField H)) x =
      Complex.I * ω * ((μ : ℂ) * energy (H x) - (ε : ℂ) * energy (E x)) := by
  have hconj : ∀ j, DifferentiableAt ℝ (fun y => conjField H y j) x :=
    fun j => differentiableAt_conj (hH j)
  rw [divergence_cross E (conjField H) x hE hconj, curl_conj H x hH,
    hMax.1, hMax.2]
  have hEE := dot_conjugate (E x)
  have hHH := conjugate_dot (H x)
  dsimp [dot, conjugate] at hEE hHH
  dsimp [dot, conjField, conjugate]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (Complex.I * ω * μ) * hHH - (Complex.I * ω * ε) * hEE

/-- Real local power conservation follows from the differential identity;
it is not supplied as a separate physical assumption. -/
theorem real_poynting_divergence_zero (ω μ ε : ℝ) (E H : Field) (x : Space)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x)
    (hMax : MaxwellAt ω μ ε E H x) :
    (divergence (crossField E (conjField H)) x).re = 0 := by
  rw [complex_poynting_identity ω μ ε E H x hE hH hMax]
  simp

/-- Coordinate partials of a C2 scalar function are differentiable. -/
theorem partial_differentiable {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (x : Space) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => dcoord f y i) x := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  exact (hd.differentiable (by simp) x).clm_apply (differentiableAt_const _)

theorem partial_second {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (x : Space) (i j : Fin 3) :
    dcoord (fun y => dcoord f y j) x i =
      fderiv ℝ (fderiv ℝ f) x (basis i) (basis j) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  simp [dcoord, fderiv_clm_apply (hd.differentiable (by simp) x)
    (differentiableAt_const (basis j))]

/-- Equality of actual mixed coordinate derivatives, from Schwarz's theorem. -/
theorem partial_comm {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (x : Space) (i j : Fin 3) :
    dcoord (fun y => dcoord f y j) x i =
      dcoord (fun y => dcoord f y i) x j := by
  rw [partial_second hf, partial_second hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) (basis i) (basis j)

def gradient (f : Space → ℂ) : Field := fun x j => dcoord f x j

theorem curl_gradient {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (x : Space) :
    curl (gradient f) x = 0 := by
  ext j
  fin_cases j <;> simp [curl, gradient, pd, partial_comm hf x 1 2,
    partial_comm hf x 2 0, partial_comm hf x 0 1]

theorem divergence_curl (F : Field) (hF : ∀ j, ContDiff ℝ 2 (fun x => F x j))
    (x : Space) : divergence (curl F) x = 0 := by
  dsimp [divergence, curl, pd]
  rw [partial_sub (partial_differentiable (hF 2) x 1)
      (partial_differentiable (hF 1) x 2),
    partial_sub (partial_differentiable (hF 0) x 2)
      (partial_differentiable (hF 2) x 0),
    partial_sub (partial_differentiable (hF 1) x 0)
      (partial_differentiable (hF 0) x 1)]
  rw [partial_comm (hF 2) x 0 1, partial_comm (hF 1) x 0 2,
    partial_comm (hF 0) x 1 2]
  ring

open MeasureTheory

theorem partial_continuous {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (fun x => dcoord f x i) :=
  (hf.continuous_fderiv le_rfl).clm_apply continuous_const

theorem partial_mul_test_integrable {f φ : Space → ℂ}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (i : Fin 3) : Integrable (fun x => dcoord f x i * φ x) :=
  ((partial_continuous hf i).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left

/-- Integration by parts on Euclidean three-space with a genuine compactly
supported C1 test function. Integrability follows from compact support. -/
theorem partial_integration_by_parts {f φ : Space → ℂ}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (i : Fin 3) :
    (∫ x, dcoord f x i * φ x) = -(∫ x, f x * dcoord φ x i) := by
  have h1 := partial_mul_test_integrable hf hφ hc i
  have h2 : Integrable (fun x => f x * dcoord φ x i) :=
    (hf.continuous.mul (partial_continuous hφ i)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis i)).mul_left
  have h0 : Integrable (fun x => f x * φ x) :=
    (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := basis i) h1 h2 h0 (hf.differentiable le_rfl) (hφ.differentiable le_rfl)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

/-- Distributional curl paired with one scalar test function per component.
The signs come from integration by parts, and require no boundary trace. -/
def weakCurlPairing (F : Field) (φ : Space → ℂ) : Vector :=
  ![(∫ x, F x 1 * dcoord φ x 2) - (∫ x, F x 2 * dcoord φ x 1),
    (∫ x, F x 2 * dcoord φ x 0) - (∫ x, F x 0 * dcoord φ x 2),
    (∫ x, F x 0 * dcoord φ x 1) - (∫ x, F x 1 * dcoord φ x 0)]

theorem curl_integration_by_parts (F : Field)
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j))
    {φ : Space → ℂ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (fun j => ∫ x, curl F x j * φ x) = weakCurlPairing F φ := by
  have hI (i j : Fin 3) := partial_mul_test_integrable (hF j) hφ hc i
  ext j
  fin_cases j <;> dsimp [curl, weakCurlPairing, pd] <;> simp only [sub_mul]
  · rw [integral_sub (hI 1 2) (hI 2 1),
      partial_integration_by_parts (hF 2) hφ hc,
      partial_integration_by_parts (hF 1) hφ hc]
    ring
  · rw [integral_sub (hI 2 0) (hI 0 2),
      partial_integration_by_parts (hF 0) hφ hc,
      partial_integration_by_parts (hF 2) hφ hc]
    ring
  · rw [integral_sub (hI 0 1) (hI 1 0),
      partial_integration_by_parts (hF 1) hφ hc,
      partial_integration_by_parts (hF 0) hφ hc]
    ring

/-- Classical C1 Maxwell fields satisfy the actual distributional curl
equations against every compactly supported C1 scalar test. This proves
the classical-to-weak implication; it does not assume an abstract weak law. -/
theorem classical_maxwell_weak_form (ω μ ε : ℝ) (E H : Field)
    (hE : ∀ j, ContDiff ℝ 1 (fun x => E x j))
    (hH : ∀ j, ContDiff ℝ 1 (fun x => H x j))
    (hMax : ∀ x, MaxwellAt ω μ ε E H x)
    {φ : Space → ℂ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing E φ = (fun j => Complex.I * ω * μ * (∫ x, H x j * φ x)) ∧
    weakCurlPairing H φ = (fun j => -Complex.I * ω * ε * (∫ x, E x j * φ x)) := by
  constructor
  · rw [← curl_integration_by_parts E hE hφ hc]
    ext j
    simp_rw [(hMax _).1, mul_assoc, integral_const_mul]
  · rw [← curl_integration_by_parts H hH hφ hc]
    ext j
    simp_rw [(hMax _).2, mul_assoc, integral_const_mul]

/-- Complexified coordinate evaluation, as an actual continuous linear map. -/
def coordinate (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

def linearPhase (q : Vector) : Space →L[ℝ] ℂ :=
  q 0 • coordinate 0 + q 1 • coordinate 1 + q 2 • coordinate 2

theorem linearPhase_basis (q : Vector) (i : Fin 3) :
    linearPhase q (basis i) = q i := by
  fin_cases i <;> simp [linearPhase, coordinate, basis, smul_eq_mul]

def exponential (q : Vector) (x : Space) : ℂ := Complex.exp (linearPhase q x)

theorem exponential_differentiable (q : Vector) (x : Space) :
    DifferentiableAt ℝ (exponential q) x :=
  (linearPhase q).differentiableAt.cexp

theorem exponential_partial (q : Vector) (x : Space) (i : Fin 3) :
    dcoord (exponential q) x i = exponential q x * q i := by
  have hd : HasFDerivAt (exponential q)
      (exponential q x • linearPhase q) x := (linearPhase q).hasFDerivAt.cexp
  simp only [dcoord, hd.fderiv, ContinuousLinearMap.smul_apply,
    linearPhase_basis, smul_eq_mul]

def exponentialField (q v : Vector) : Field :=
  fun x j => v j * exponential q x

theorem exponentialField_differentiable (q v : Vector) (x : Space) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => exponentialField q v y j) x :=
  (differentiableAt_const (v j)).mul (exponential_differentiable q x)

theorem exponentialField_partial (q v : Vector) (x : Space) (i j : Fin 3) :
    dcoord (fun y => exponentialField q v y j) x i =
      q i * v j * exponential q x := by
  change dcoord (fun y => v j * exponential q y) x i = _
  rw [partial_mul (differentiableAt_const (v j)) (exponential_differentiable q x)]
  rw [exponential_partial]
  have hz : dcoord (fun _ : Space => v j) x i = 0 := by simp [dcoord]
  rw [hz]
  ring

theorem curl_exponentialField (q v : Vector) (x : Space) :
    curl (exponentialField q v) x =
      (fun j => crossProduct q v j * exponential q x) := by
  ext j
  fin_cases j <;> simp [curl, pd, exponentialField_partial, cross_apply] <;> ring

/-- Algebraic amplitude constraints produce actual differentiable Maxwell
fields; the derivative calculation is discharged by curl_exponentialField. -/
theorem exponential_maxwell (q e h : Vector) (ω μ ε : ℝ)
    (he : crossProduct q e = fun j => Complex.I * ω * μ * h j)
    (hh : crossProduct q h = fun j => -Complex.I * ω * ε * e j)
    (x : Space) :
    MaxwellAt ω μ ε (exponentialField q e) (exponentialField q h) x := by
  constructor
  · rw [curl_exponentialField, he]
    ext j
    simp [exponentialField, mul_assoc]
  · rw [curl_exponentialField, hh]
    ext j
    simp [exponentialField, mul_assoc]

def vacuumWaveVector : Vector := ![0, 0, Complex.I]
def vacuumElectric : Vector := ![1, 0, 0]
def vacuumMagnetic : Vector := ![0, 1, 0]

/-- An explicit nonzero plane-wave solution in vacuum at normalized
positive frequency one; no Maxwell equations are assumed as hypotheses. -/
theorem vacuum_plane_wave (x : Space) :
    MaxwellAt 1 1 1 (exponentialField vacuumWaveVector vacuumElectric)
      (exponentialField vacuumWaveVector vacuumMagnetic) x := by
  apply exponential_maxwell
  · ext j
    fin_cases j <;> simp [vacuumWaveVector, vacuumElectric, vacuumMagnetic, cross_apply]
  · ext j
    fin_cases j <;> simp [vacuumWaveVector, vacuumElectric, vacuumMagnetic, cross_apply]

def evanescentWaveVector (s : ℝ) : Vector :=
  ![Complex.I * (5 / 4 : ℂ), 0, (s : ℂ) * (3 / 4 : ℂ)]

def evanescentElectric : Vector := ![0, 1, 0]

def evanescentMagnetic (s : ℝ) : Vector :=
  ![Complex.I * (s : ℂ) * (3 / 4 : ℂ), 0, (5 / 4 : ℂ)]

/-- A growing/decaying evanescent exponential is a genuine local Maxwell
solution for either sign. This does not assert physical global excitation. -/
theorem evanescent_wave (s : ℝ) (hs : s = 1 ∨ s = -1) (x : Space) :
    MaxwellAt 1 1 1
      (exponentialField (evanescentWaveVector s) evanescentElectric)
      (exponentialField (evanescentWaveVector s) (evanescentMagnetic s)) x := by
  apply exponential_maxwell
  · ext j
    rcases hs with rfl | rfl <;> fin_cases j <;>
      norm_num [evanescentWaveVector, evanescentElectric, evanescentMagnetic,
        cross_apply, Complex.ext_iff, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]

  · ext j
    rcases hs with rfl | rfl <;> fin_cases j <;>
      norm_num [evanescentWaveVector, evanescentElectric, evanescentMagnetic,
        cross_apply, Complex.ext_iff, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]

def normalPower (e h : Vector) : ℝ := (crossProduct e (conjugate h) 2).re / 2

def evanescentE (s : ℝ) : Field :=
  exponentialField (evanescentWaveVector s) evanescentElectric

def evanescentH (s : ℝ) : Field :=
  exponentialField (evanescentWaveVector s) (evanescentMagnetic s)

def pairedE : Field := fun x j => evanescentE (-1) x j + Complex.I * evanescentE 1 x j
def pairedH : Field := fun x j => evanescentH (-1) x j + Complex.I * evanescentH 1 x j

/-- The coherent pair is an actual Maxwell solution everywhere in Euclidean
space. Its exponential growth prevents a claim of finite incident power. -/
theorem paired_evanescent_maxwell (x : Space) : MaxwellAt 1 1 1 pairedE pairedH x := by
  simpa only [one_mul] using
    maxwell_superposition 1 1 1 (evanescentE (-1)) (evanescentH (-1))
      (evanescentE 1) (evanescentH 1) 1 Complex.I x
      (exponentialField_differentiable _ _ x)
      (exponentialField_differentiable _ _ x)
      (exponentialField_differentiable _ _ x)
      (exponentialField_differentiable _ _ x)
      (evanescent_wave (-1) (Or.inr rfl) x) (evanescent_wave 1 (Or.inl rfl) x)

/-- Every individual growing/decaying evanescent wave has zero real normal
power at the origin. -/
theorem evanescent_zero_normal_power (s : ℝ) :
    normalPower (evanescentE s 0) (evanescentH s 0) = 0 := by
  norm_num [normalPower, evanescentE, evanescentH, exponentialField, exponential,
    evanescentElectric, evanescentMagnetic, conjugate, cross_apply,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_ofNat]

/-- Two individually zero-flux Maxwell solutions can carry strictly positive
normal power after coherent superposition. This is a local flux theorem. -/
theorem paired_evanescent_positive_power : normalPower (pairedE 0) (pairedH 0) = 3 / 4 := by
  norm_num [normalPower, pairedE, pairedH, evanescentE, evanescentH,
    exponentialField, exponential, evanescentElectric, evanescentMagnetic,
    conjugate, cross_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_ofNat]

theorem opposite_evanescent_product (x : Space) :
    exponential (evanescentWaveVector (-1)) x *
      conj (exponential (evanescentWaveVector 1) x) = 1 := by
  unfold exponential
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have hp : linearPhase (evanescentWaveVector (-1)) x +
      conj (linearPhase (evanescentWaveVector 1) x) = 0 := by
    simp [linearPhase, evanescentWaveVector, coordinate, smul_eq_mul,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_ofNat]
    ring
  rw [hp, Complex.exp_zero]

theorem paired_power_algebra (a b c : ℂ) (hab : a * conj b = 1) :
    normalPower ![0, a + Complex.I * b, 0]
      ![-Complex.I * (3 / 4 : ℂ) * a - (3 / 4 : ℂ) * b, 0, c] = 3 / 4 := by
  have hr := congrArg Complex.re hab
  norm_num [normalPower, conjugate, cross_apply, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_ofNat, Complex.mul_re, Complex.mul_im] at *
  linarith

/-- The coherent pair carries the same positive normal power throughout
space. Its infinite transverse extent and exponential growth are explicit. -/
theorem paired_evanescent_power_everywhere (x : Space) :
    normalPower (pairedE x) (pairedH x) = 3 / 4 := by
  have he : pairedE x = ![0,
      exponential (evanescentWaveVector (-1)) x +
        Complex.I * exponential (evanescentWaveVector 1) x, 0] := by
    ext j
    fin_cases j <;> simp [pairedE, evanescentE, exponentialField, evanescentElectric]
  have hh : pairedH x = ![
      -Complex.I * (3 / 4 : ℂ) * exponential (evanescentWaveVector (-1)) x -
        (3 / 4 : ℂ) * exponential (evanescentWaveVector 1) x,
      0, (5 / 4 : ℂ) * exponential (evanescentWaveVector (-1)) x +
        Complex.I * (5 / 4 : ℂ) * exponential (evanescentWaveVector 1) x] := by
    ext j
    fin_cases j <;> norm_num [pairedH, evanescentH, exponentialField, evanescentMagnetic,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · ring_nf
      simp [Complex.I_sq]
      ring
    · ring
  rw [he, hh]
  exact paired_power_algebra _ _ _ (opposite_evanescent_product x)

theorem evanescent_zero_normal_power_everywhere (s : ℝ) (x : Space) :
    normalPower (evanescentE s x) (evanescentH s x) = 0 := by
  simp [normalPower, evanescentE, evanescentH, exponentialField,
    evanescentElectric, evanescentMagnetic, conjugate, cross_apply,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_ofNat,
    Complex.mul_re, Complex.mul_im]
  ring
end OQ14.Maxwell

#print axioms OQ14.Maxwell.divergence_cross
#print axioms OQ14.Maxwell.curl_conj
#print axioms OQ14.Maxwell.complex_poynting_identity
#print axioms OQ14.Maxwell.real_poynting_divergence_zero
#print axioms OQ14.Maxwell.vacuum_plane_wave
#print axioms OQ14.Maxwell.evanescent_wave
#print axioms OQ14.Maxwell.curl_gradient
#print axioms OQ14.Maxwell.divergence_curl
#print axioms OQ14.Maxwell.maxwell_superposition
#print axioms OQ14.Maxwell.paired_evanescent_maxwell
#print axioms OQ14.Maxwell.evanescent_zero_normal_power
#print axioms OQ14.Maxwell.paired_evanescent_positive_power
#print axioms OQ14.Maxwell.partial_integration_by_parts
#print axioms OQ14.Maxwell.curl_integration_by_parts
#print axioms OQ14.Maxwell.classical_maxwell_weak_form
#print axioms OQ14.Maxwell.maxwell_curl_curl
#print axioms OQ14.Maxwell.paired_evanescent_power_everywhere
#print axioms OQ14.Maxwell.evanescent_zero_normal_power_everywhere
