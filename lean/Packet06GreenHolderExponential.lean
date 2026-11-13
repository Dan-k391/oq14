import Packet06GreenHolderPointwise
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderExponential

/-- Global quantitative complex exponential difference estimate, without a smallness assumption. -/
theorem exp_difference (z w : ℂ) :
    ‖Complex.exp z - Complex.exp w‖ ≤
      Real.exp ‖w‖ * (‖z-w‖ * Real.exp ‖z-w‖) := by
  have hexp : Complex.exp z - Complex.exp w = Complex.exp w * (Complex.exp (z-w)-1) := by
    have hs : w + (z-w) = z := by abel
    rw [mul_sub, mul_one, ← Complex.exp_add, hs]
  rw [hexp, norm_mul]
  apply mul_le_mul (Complex.norm_exp_le_exp_norm w) ?_ (norm_nonneg _) (Real.exp_pos _).le
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (z-w) 1

/-- On any common norm ball the exponential is Lipschitz with an explicit uniform constant. -/
theorem exp_difference_bounded (z w : ℂ) (M : ℝ) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖Complex.exp z - Complex.exp w‖ ≤
      (Real.exp M * Real.exp (2*M)) * ‖z-w‖ := by
  have hm : 0 ≤ M := (norm_nonneg z).trans hz
  have hd : ‖z-w‖ ≤ 2*M := by
    calc
      ‖z-w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2*M := by linarith
  calc
    ‖Complex.exp z - Complex.exp w‖ ≤
      Real.exp ‖w‖ * (‖z-w‖ * Real.exp ‖z-w‖) := exp_difference z w
    _ ≤ Real.exp M * (‖z-w‖ * Real.exp (2*M)) := by
      gcongr
    _ = _ := by ring

/-- The radial Helmholtz exponential has a uniform Lipschitz bound on a common spatial ball. -/
theorem radial_exp_difference (z : ℂ) (Z T : ℝ) (hZ : ‖z‖ ≤ Z)
    (u v : OQ14.Maxwell.Space) (hu : ‖u‖ ≤ T) (hv : ‖v‖ ≤ T) :
    ‖Complex.exp (Complex.I*z*(‖u‖ : ℂ)) - Complex.exp (Complex.I*z*(‖v‖ : ℂ))‖ ≤
      (Real.exp (Z*T) * Real.exp (2*(Z*T))) * (Z*‖u-v‖) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hT0 : 0 ≤ T := (norm_nonneg u).trans hu
  have harg (w : OQ14.Maxwell.Space) (hw : ‖w‖ ≤ T) :
      ‖Complex.I*z*(‖w‖ : ℂ)‖ ≤ Z*T := by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg w)]
    exact mul_le_mul hZ hw (norm_nonneg _) hZ0
  have hd : ‖Complex.I*z*(‖u‖ : ℂ) - Complex.I*z*(‖v‖ : ℂ)‖ ≤ Z*‖u-v‖ := by
    rw [← mul_sub, norm_mul]
    simp only [norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul hZ (abs_norm_sub_norm_le u v) (abs_nonneg _) hZ0
  exact (exp_difference_bounded _ _ (Z*T) (harg u hu) (harg v hv)).trans
    (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
#print axioms OQ14.Packet06GreenHolderExponential.radial_exp_difference
#print axioms OQ14.Packet06GreenHolderExponential.exp_difference
#print axioms OQ14.Packet06GreenHolderExponential.exp_difference_bounded
end OQ14.Packet06GreenHolderExponential
