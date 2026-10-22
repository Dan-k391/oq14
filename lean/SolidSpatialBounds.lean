import SolidRadialDerivatives
import SolidScalarHelmholtz
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual compact spatial derivative bounds for regular solid waves. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SolidSpatialBounds

open Complex Set OQ14.Maxwell OQ14.SolidRadialSeries OQ14.SolidRadialDerivatives

/-- The literal supremum norm of the j-th spatial derivative on a ball. -/
def jetSup (f : Space → ℂ) (j : ℕ) (b : ℝ) : ℝ :=
  sSup ((fun x => ‖iteratedFDeriv ℝ j f x‖) '' Metric.closedBall 0 b)

/-- An actual finite compact jet norm, retaining the polynomial normalization. -/
def jetNorm (f : Space → ℂ) (N : ℕ) (b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), jetSup f j b

theorem jetSup_nonneg (f : Space → ℂ) (j : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : 0 ≤ jetSup f j b := by
  have hc := hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  have hbd := (isCompact_closedBall (0 : Space) b).bddAbove_image hc.norm.continuousOn
  exact (norm_nonneg (iteratedFDeriv ℝ j f 0)).trans
    (le_csSup hbd (mem_image_of_mem _ (by simpa using hb)))

theorem jetNorm_nonneg (f : Space → ℂ) (N : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : 0 ≤ jetNorm f N b :=
  Finset.sum_nonneg (fun j _ => jetSup_nonneg f j b hb hf)

theorem norm_derivative_le_jetNorm (f : Space → ℂ) (N j : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hj : j ≤ N) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ jetNorm f N b := by
  have hc := hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  have hbd := (isCompact_closedBall (0 : Space) b).bddAbove_image hc.norm.continuousOn
  calc
    _ ≤ jetSup f j b := le_csSup hbd (mem_image_of_mem _ (by simpa using hx))
    _ ≤ jetNorm f N b := Finset.single_le_sum (fun i _ => jetSup_nonneg f i b hb hf)
      (Finset.mem_range.mpr (by omega))

theorem real_iteratedFDeriv_F (l j : ℕ) (t : ℂ) :
    iteratedFDeriv ℝ j (F l) t=(iteratedFDeriv ℂ j (F l) t).restrictScalars ℝ := by
  have hs := ((F_contDiff l).contDiffOn.ftaylorSeriesWithin uniqueDiffOn_univ).restrictScalars ℝ
  have h := hs.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j)
    (by exact_mod_cast le_top) uniqueDiffOn_univ (mem_univ t)
  simpa only [FormalMultilinearSeries.restrictScalars,ftaylorSeriesWithin,iteratedFDerivWithin_univ] using h.symm

theorem real_iteratedFDeriv_F_norm (l j : ℕ) (t : ℂ) :
    ‖iteratedFDeriv ℝ j (F l) t‖ ≤
      RiccatiSeriesCoefficients.amplitude l 0*Real.exp (‖t‖/2) := by
  rw [real_iteratedFDeriv_F,ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact iteratedDeriv_norm_bound l j t

def squaredArgument (q : ℂ) (x : Space) : ℂ := q^2*(‖x‖^2 : ℝ)

def factor (l : ℕ) (q : ℂ) (x : Space) : ℂ := F l (squaredArgument q x)

theorem squaredArgument_contDiff (q : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (squaredArgument q) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ))

theorem factor_contDiff (l : ℕ) (q : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (factor l q) :=
  ((F_contDiff l).restrict_scalars ℝ).comp (squaredArgument_contDiff q)

def compositionScale (q : ℂ) (N : ℕ) (b : ℝ) : ℝ :=
  1+jetNorm (squaredArgument q) N b

theorem compositionScale_ge_one (q : ℂ) (N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    1 ≤ compositionScale q N b := by
  exact le_add_of_nonneg_right (jetNorm_nonneg _ N b hb (squaredArgument_contDiff q))

theorem squaredArgument_norm_le (q : ℂ) (b : ℝ) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖squaredArgument q x‖ ≤ ‖q^2‖*b^2 := by
  simp only [squaredArgument,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖x‖)]
  gcongr

theorem factor_derivative_bound (l : ℕ) (q : ℂ) (N j : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hj : j ≤ N) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (factor l q) x‖ ≤
      (j.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^j := by
  apply norm_iteratedFDeriv_comp_le ((F_contDiff l).restrict_scalars ℝ)
    (squaredArgument_contDiff q) (by exact_mod_cast le_top)
  · intro i hi
    refine (real_iteratedFDeriv_F_norm l i _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (RiccatiSeriesCoefficients.amplitude_pos l 0).le
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squaredArgument_norm_le q b x hx) (by norm_num))
  · intro i hi hiN
    calc
      _ ≤ jetNorm (squaredArgument q) N b :=
        norm_derivative_le_jetNorm _ N i b hb (squaredArgument_contDiff q) (hiN.trans hj) x hx
      _ ≤ compositionScale q N b := by dsimp [compositionScale]; linarith
      _ ≤ compositionScale q N b^i := le_self_pow₀ (compositionScale_ge_one q N b hb) (by omega)

theorem factor_derivative_uniform_bound (l : ℕ) (q : ℂ) (N j : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hj : j ≤ N) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (factor l q) x‖ ≤
      (N.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N := by
  refine (factor_derivative_bound l q N j b hb hj x hx).trans ?_
  have ha := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity)
  · exact pow_le_pow_right₀ (compositionScale_ge_one q N b hb) hj
  · exact pow_nonneg ((compositionScale_ge_one q N b hb).trans' (by norm_num)) _
  · positivity

theorem wave_derivative_bound (l : ℕ) (q : ℂ) (p : HarmonicPolynomial.Poly)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l q p) x‖ ≤
      2^N*((N.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N)*
        jetNorm (HarmonicPolynomial.complexEvaluate p) N b := by
  let C := (N.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N
  let P := jetNorm (HarmonicPolynomial.complexEvaluate p) N b
  have hP : 0 ≤ P := jetNorm_nonneg _ N b hb (HarmonicPolynomial.complexEvaluate_regular p)
  have hC : 0 ≤ C := by
    have ha := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
    have hD := (compositionScale_ge_one q N b hb).trans' (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [C]
    positivity
  change ‖iteratedFDeriv ℝ N (fun y => factor l q y*HarmonicPolynomial.complexEvaluate p y) x‖ ≤ 2^N*C*P
  calc
    _ ≤ ∑ i ∈ Finset.range (N+1), (N.choose i : ℝ)*‖iteratedFDeriv ℝ i (factor l q) x‖*
        ‖iteratedFDeriv ℝ (N-i) (HarmonicPolynomial.complexEvaluate p) x‖ :=
      norm_iteratedFDeriv_mul_le (factor_contDiff l q) (HarmonicPolynomial.complexEvaluate_regular p)
        x (by exact_mod_cast le_top)
    _ ≤ ∑ i ∈ Finset.range (N+1), (N.choose i : ℝ)*C*P := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (factor_derivative_uniform_bound l q N i b hb hiN x hx) (by positivity)
      · exact norm_derivative_le_jetNorm _ N (N-i) b hb
          (HarmonicPolynomial.complexEvaluate_regular p) (Nat.sub_le _ _) x hx
      · exact norm_nonneg _
      · exact mul_nonneg (by positivity) hC
    _ = 2^N*C*P := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]

end OQ14.SolidSpatialBounds

#print axioms OQ14.SolidSpatialBounds.jetSup_nonneg
#print axioms OQ14.SolidSpatialBounds.jetNorm_nonneg
#print axioms OQ14.SolidSpatialBounds.norm_derivative_le_jetNorm
#print axioms OQ14.SolidSpatialBounds.real_iteratedFDeriv_F
#print axioms OQ14.SolidSpatialBounds.real_iteratedFDeriv_F_norm
#print axioms OQ14.SolidSpatialBounds.squaredArgument_contDiff
#print axioms OQ14.SolidSpatialBounds.factor_contDiff
#print axioms OQ14.SolidSpatialBounds.compositionScale_ge_one
#print axioms OQ14.SolidSpatialBounds.squaredArgument_norm_le
#print axioms OQ14.SolidSpatialBounds.factor_derivative_bound
#print axioms OQ14.SolidSpatialBounds.factor_derivative_uniform_bound
#print axioms OQ14.SolidSpatialBounds.wave_derivative_bound
