import RadialMoment

/-! # Actual weighted radial moment coefficient derivatives -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.RadialMomentWeights

def coefficientA (l : ℕ) (U : ℝ → ℂ) (r : ℝ) : ℂ := (r : ℂ)^(l+2)*U r

def coefficientAD (l : ℕ) (U UD : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((l : ℂ)+2)*(r : ℂ)^(l+1)*U r + (r : ℂ)^(l+2)*UD r

def coefficientADD (l : ℕ) (U UD UDD : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((l : ℂ)+2)*((l : ℂ)+1)*(r : ℂ)^l*U r +
    2*((l : ℂ)+2)*(r : ℂ)^(l+1)*UD r + (r : ℂ)^(l+2)*UDD r

def coefficientB (l : ℕ) (U : ℝ → ℂ) (r : ℝ) : ℂ :=
  (2*(l : ℂ)+2)*(r : ℂ)^(l+1)*U r

def coefficientBD (l : ℕ) (U UD : ℝ → ℂ) (r : ℝ) : ℂ :=
  (2*(l : ℂ)+2)*(((l : ℂ)+1)*(r : ℂ)^l*U r + (r : ℂ)^(l+1)*UD r)

def coefficientC (l : ℕ) (k : ℂ) (U : ℝ → ℂ) (r : ℝ) : ℂ :=
  k^2*(r : ℂ)^(l+2)*U r

theorem complex_radius_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
  simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt

theorem complex_power_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)^n) ((n : ℂ)*(r : ℂ)^(n-1)) r := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_pow n r)
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using hd
theorem coefficientA_hasDerivAt (l : ℕ) (U UD : ℝ → ℂ) (r : ℝ)
    (hU : HasDerivAt U (UD r) r) :
    HasDerivAt (coefficientA l U) (coefficientAD l U UD r) r := by
  convert (complex_power_hasDerivAt (l+2) r).mul hU using 1
  simp [coefficientAD, Nat.add_sub_cancel]

theorem coefficientAD_hasDerivAt (l : ℕ) (U UD UDD : ℝ → ℂ) (r : ℝ)
    (hU : HasDerivAt U (UD r) r) (hUD : HasDerivAt UD (UDD r) r) :
    HasDerivAt (coefficientAD l U UD) (coefficientADD l U UD UDD r) r := by
  convert ((((complex_power_hasDerivAt (l+1) r).const_mul ((l : ℂ)+2)).mul hU).add
    ((complex_power_hasDerivAt (l+2) r).mul hUD)) using 1
  simp only [coefficientADD, show l+2-1=l+1 by omega, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem coefficientB_hasDerivAt (l : ℕ) (U UD : ℝ → ℂ) (r : ℝ)
    (hU : HasDerivAt U (UD r) r) :
    HasDerivAt (coefficientB l U) (coefficientBD l U UD r) r := by
  have hf : coefficientB l U = fun t : ℝ => (2*(l : ℂ)+2)*((t : ℂ)^(l+1)*U t) := by
    funext t
    unfold coefficientB
    ring
  rw [hf]
  convert (((complex_power_hasDerivAt (l+1) r).mul hU).const_mul
    (2*(l : ℂ)+2)) using 1
  simp only [coefficientBD, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
theorem coefficient_residual (l : ℕ) (k : ℂ) (U UD UDD : ℝ → ℂ) (r : ℝ) :
    coefficientADD l U UD UDD r - coefficientBD l U UD r + coefficientC l k U r =
      (r : ℂ)^l*((r : ℂ)^2*UDD r+2*(r : ℂ)*UD r+
        (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*U r) := by
  simp only [coefficientADD, coefficientBD, coefficientC, pow_add, pow_one]
  ring


theorem coefficientADD_continuousOn (l : ℕ) (s : Set ℝ) (U UD UDD : ℝ → ℂ)
    (hU : ContinuousOn U s) (hUD : ContinuousOn UD s) (hUDD : ContinuousOn UDD s) :
    ContinuousOn (coefficientADD l U UD UDD) s := by
  unfold coefficientADD
  fun_prop

theorem coefficientBD_continuousOn (l : ℕ) (s : Set ℝ) (U UD : ℝ → ℂ)
    (hU : ContinuousOn U s) (hUD : ContinuousOn UD s) :
    ContinuousOn (coefficientBD l U UD) s := by
  unfold coefficientBD
  fun_prop

theorem coefficientC_continuousOn (l : ℕ) (k : ℂ) (s : Set ℝ) (U : ℝ → ℂ)
    (hU : ContinuousOn U s) : ContinuousOn (coefficientC l k U) s := by
  unfold coefficientC
  fun_prop
end OQ14.RadialMomentWeights

#print axioms OQ14.RadialMomentWeights.complex_radius_hasDerivAt
#print axioms OQ14.RadialMomentWeights.complex_power_hasDerivAt
#print axioms OQ14.RadialMomentWeights.coefficientA_hasDerivAt
#print axioms OQ14.RadialMomentWeights.coefficientAD_hasDerivAt
#print axioms OQ14.RadialMomentWeights.coefficientB_hasDerivAt
#print axioms OQ14.RadialMomentWeights.coefficient_residual
#print axioms OQ14.RadialMomentWeights.coefficientADD_continuousOn
#print axioms OQ14.RadialMomentWeights.coefficientBD_continuousOn
#print axioms OQ14.RadialMomentWeights.coefficientC_continuousOn
