import SolidSpatialBounds
import ScalarExterior

/-! Actual coefficient-normalized compact jets of spatial polynomials. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.PolynomialJetBounds

open Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SolidSpatialBounds

theorem mul_jet_bound (f g : Space → ℂ) (N j : ℕ) (x : Space) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfj : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgj : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i g x‖ ≤ B) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^N*A*B := by
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (j-i) g x‖ := norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast le_top)
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfj i ((Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hi)).trans hj)) (by positivity))
        (hgj (j-i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (mul_nonneg (by positivity) hA)
    _ = 2^j*A*B := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 2^N*A*B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hA) hB

theorem coordinate_jet_bound (i : Fin 3) (j : ℕ) (x : Space) (B : ℝ)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y : Space => (y i : ℂ)) x‖ ≤ B := by
  change ‖iteratedFDeriv ℝ j (ScalarExterior.coordinateCLM i) x‖ ≤ B
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have hc : ‖ScalarExterior.coordinateCLM i x‖ ≤ ‖x‖ := by
      simpa only [ScalarExterior.coordinateCLM_apply,Complex.norm_real] using PiLp.norm_apply_le x i
    exact hc.trans hx
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (ScalarExterior.coordinateCLM i) = fun _ => ScalarExterior.coordinateCLM i :=
      funext (fun _ => (ScalarExterior.coordinateCLM i).hasFDerivAt.fderiv)
    rw [hd]
    by_cases hj : j=0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      exact (ScalarExterior.coordinateCLM_norm_le i).trans hB
    · rw [iteratedFDeriv_const_of_ne hj]
      simpa using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hB)

theorem coordinate_power_jet_bound (i : Fin 3) (e N j : ℕ) (x : Space) (B : ℝ)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (fun y : Space => (y i : ℂ)^e) x‖ ≤ (2^N*B)^e := by
  induction e generalizing j with
  | zero =>
    simp only [pow_zero]
    by_cases hj0 : j=0
    · subst j; simp
    · rw [iteratedFDeriv_const_of_ne hj0]; simp
  | succ e ih =>
    simp only [pow_succ]
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space => (y i : ℂ)) :=
      (ScalarExterior.coordinateCLM i).contDiff
    have h := mul_jet_bound (fun y : Space => (y i : ℂ)^e) (fun y : Space => (y i : ℂ)) N j x
      ((2^N*B)^e) B (by positivity) (by linarith) (hc.pow e) hc
      (fun a ha => ih a ha) (fun a _ => coordinate_jet_bound i a x B hB hx) hj
    convert h using 1; ring

def monomialValue (d : Fin 3 →₀ ℕ) (x : Space) : ℂ := ∏ i : Fin 3, (x i : ℂ)^(d i)

theorem monomialValue_contDiff (d : Fin 3 →₀ ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (monomialValue d) :=
  contDiff_prod (fun i _ => (ScalarExterior.coordinateCLM i).contDiff.pow (d i))

theorem monomialValue_jet_bound (d : Fin 3 →₀ ℕ) (N j : ℕ) (x : Space) (B : ℝ)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (monomialValue d) x‖ ≤
      (2^N)^2*(2^N*B)^(d 0+d 1+d 2) := by
  let C := 2^N*B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space => (y i : ℂ)^(d i)) :=
    (ScalarExterior.coordinateCLM i).contDiff.pow (d i)
  have h01 (a : ℕ) (ha : a ≤ N) :
      ‖iteratedFDeriv ℝ a (fun y : Space => (y 0 : ℂ)^(d 0)*(y 1 : ℂ)^(d 1)) x‖ ≤
        2^N*C^(d 0)*C^(d 1) :=
    mul_jet_bound _ _ N a x _ _ (pow_nonneg hC _) (pow_nonneg hC _) (hc 0) (hc 1)
      (fun a ha => coordinate_power_jet_bound 0 (d 0) N a x B hB hx ha)
      (fun a ha => coordinate_power_jet_bound 1 (d 1) N a x B hB hx ha) ha
  have h := mul_jet_bound _ _ N j x (2^N*C^(d 0)*C^(d 1)) (C^(d 2)) (by positivity)
    (pow_nonneg hC _) ((hc 0).mul (hc 1)) (hc 2) h01
    (fun a ha => coordinate_power_jet_bound 2 (d 2) N a x B hB hx ha) hj
  change ‖iteratedFDeriv ℝ j (fun y => (y 0 : ℂ)^(d 0)*(y 1 : ℂ)^(d 1)*(y 2 : ℂ)^(d 2)) x‖ ≤ _ at h
  have heq : monomialValue d=(fun y : Space => (y 0 : ℂ)^(d 0)*(y 1 : ℂ)^(d 1)*(y 2 : ℂ)^(d 2)) := by
    funext y
    simp [monomialValue,Fin.prod_univ_three]
  rw [heq]
  simpa only [C,pow_add,pow_two,mul_assoc] using h

def coefficientNorm (p : Poly) : ℝ := ∑ d ∈ p.support, ‖MvPolynomial.coeff d p‖

theorem coefficientNorm_nonneg (p : Poly) : 0 ≤ coefficientNorm p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem complexEvaluate_monomial (d : Fin 3 →₀ ℕ) (a : ℝ) :
    complexEvaluate (MvPolynomial.monomial d a)=(fun x => (a : ℂ)*monomialValue d x) := by
  funext x
  simp only [complexEvaluate,evaluate,MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [monomialValue]

theorem complexEvaluate_as_sum (p : Poly) :
    complexEvaluate p=(fun x => ∑ d ∈ p.support, ((MvPolynomial.coeff d p : ℝ) : ℂ)*monomialValue d x) := by
  have hsum : complexEvaluate p=complexEvaluate (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) :=
    congrArg complexEvaluate p.as_sum
  rw [hsum]
  funext x
  simp only [complexEvaluate,evaluate,map_sum,Complex.ofReal_sum]
  change (∑ d ∈ p.support, complexEvaluate (MvPolynomial.monomial d (MvPolynomial.coeff d p)) x)=_
  simp only [complexEvaluate_monomial]

theorem monomial_jet_bound (d : Fin 3 →₀ ℕ) (a : ℝ) (N j : ℕ) (x : Space) (B : ℝ)
    (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (complexEvaluate (MvPolynomial.monomial d a)) x‖ ≤
      ‖a‖*((2^N)^2*(2^N*B)^(d 0+d 1+d 2)) := by
  rw [complexEvaluate_monomial]
  change ‖iteratedFDeriv ℝ j ((a : ℂ) • monomialValue d) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply ((monomialValue_contDiff d).of_le (by exact_mod_cast le_top)).contDiffAt,
    norm_smul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (monomialValue_jet_bound d N j x B hB hx hj) (norm_nonneg _)

theorem support_degree (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (d : Fin 3 →₀ ℕ) (hd : d ∈ p.support) : d 0+d 1+d 2=l := by
  have hdeg : d.degree=l := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero hne)
  change d.sum (fun _ n => n)=l at hdeg
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
  simpa only [Fin.sum_univ_three] using hdeg

theorem homogeneous_jet_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (N j : ℕ) (x : Space) (B : ℝ) (hB : 1 ≤ B) (hx : ‖x‖ ≤ B) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (complexEvaluate p) x‖ ≤
      coefficientNorm p*(2^N)^2*(2^N*B)^l := by
  have hsum : complexEvaluate p=(fun x => ∑ d ∈ p.support,
      complexEvaluate (MvPolynomial.monomial d (MvPolynomial.coeff d p)) x) := by
    rw [complexEvaluate_as_sum]
    simp only [complexEvaluate_monomial]
  rw [hsum,iteratedFDeriv_sum (fun d _ => (complexEvaluate_regular
    (MvPolynomial.monomial d (MvPolynomial.coeff d p))).of_le (by exact_mod_cast le_top)),Finset.sum_apply]
  calc
    _ ≤ ∑ d ∈ p.support, ‖iteratedFDeriv ℝ j
        (complexEvaluate (MvPolynomial.monomial d (MvPolynomial.coeff d p))) x‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ p.support, ‖MvPolynomial.coeff d p‖*((2^N)^2*(2^N*B)^l) := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [support_degree p l hp d hd] using
        monomial_jet_bound d (MvPolynomial.coeff d p) N j x B hB hx hj
    _ = coefficientNorm p*(2^N)^2*(2^N*B)^l := by
      rw [← Finset.sum_mul]
      dsimp [coefficientNorm]
      ring

theorem homogeneous_compact_jet_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    jetNorm (complexEvaluate p) N b ≤
      ((N : ℝ)+1)*coefficientNorm p*(2^N)^2*(2^N*max 1 b)^l := by
  let C := coefficientNorm p*(2^N)^2*(2^N*max 1 b)^l
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), C := by
      apply Finset.sum_le_sum
      intro j hj
      apply csSup_le
      · exact ⟨_, Set.mem_image_of_mem _ (show (0 : Space) ∈ Metric.closedBall 0 b by simpa using hb)⟩
      · rintro _ ⟨x,hx,rfl⟩
        have hxb : ‖x‖ ≤ b := by simpa using hx
        exact homogeneous_jet_bound p l hp N j x (max 1 b) (le_max_left _ _)
          (hxb.trans (le_max_right _ _)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ((N : ℝ)+1)*coefficientNorm p*(2^N)^2*(2^N*max 1 b)^l := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,C]
      ring

theorem solid_wave_coefficient_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (q : ℂ) (N : ℕ) (b : ℝ) (hb : 0 ≤ b) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l q p) x‖ ≤
      2^N*((N.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N)*
        (((N : ℝ)+1)*coefficientNorm p*(2^N)^2*(2^N*max 1 b)^l) := by
  refine (wave_derivative_bound l q p N b hb x hx).trans ?_
  apply mul_le_mul_of_nonneg_left (homogeneous_compact_jet_bound p l hp N b hb)
  have ha := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
  have hD := (compositionScale_ge_one q N b hb).trans' (by norm_num : (0 : ℝ) ≤ 1)
  positivity

end OQ14.PolynomialJetBounds

#print axioms OQ14.PolynomialJetBounds.mul_jet_bound
#print axioms OQ14.PolynomialJetBounds.coordinate_jet_bound
#print axioms OQ14.PolynomialJetBounds.coordinate_power_jet_bound
#print axioms OQ14.PolynomialJetBounds.monomialValue_contDiff
#print axioms OQ14.PolynomialJetBounds.monomialValue_jet_bound
#print axioms OQ14.PolynomialJetBounds.coefficientNorm_nonneg
#print axioms OQ14.PolynomialJetBounds.complexEvaluate_monomial
#print axioms OQ14.PolynomialJetBounds.complexEvaluate_as_sum
#print axioms OQ14.PolynomialJetBounds.monomial_jet_bound
#print axioms OQ14.PolynomialJetBounds.support_degree
#print axioms OQ14.PolynomialJetBounds.homogeneous_jet_bound
#print axioms OQ14.PolynomialJetBounds.homogeneous_compact_jet_bound
#print axioms OQ14.PolynomialJetBounds.solid_wave_coefficient_bound
