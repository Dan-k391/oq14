import ScalarGreenJump

/-! Exact physical normalization obtained from the actual Green source jump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ScalarGreenNormalization
open Complex Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.ScalarGreenJump
  OQ14.ScalarGreenMoment OQ14.RadialRellich

theorem profile_wronskian (l : ℕ) (k : ℂ) (hk : k ≠ 0) (s : ℝ) (hs : 0 < s) :
    innerProfile l k s*deriv (outerProfile l k) s-
      outerProfile l k s*deriv (innerProfile l k) s=I*k/(s : ℂ)^2 := by
  have hi := RadialQuotient.profile_hasDerivAt 0 (RadialOriginSelection.regular l k)
    (RadialOriginSelection.regularD l k) s hs.ne' (RadialOriginSelection.regular_hasDerivAt l k s)
  have ho := RadialQuotient.profile_hasDerivAt 0 (outgoing l k) (outgoingD l k) s hs.ne'
    (outgoing_hasDerivAt l k hk s hs.ne')
  change innerProfile l k s*deriv (RadialQuotient.profile 0 (outgoing l k)) s-
    outerProfile l k s*deriv (RadialQuotient.profile 0 (RadialOriginSelection.regular l k)) s=_
  rw [hi.deriv,ho.deriv]
  have hw := RadialOriginSelection.regular_outgoing_wronskian l k hk s hs.ne'
  have hsc : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  simp only [innerProfile,outerProfile,RadialQuotient.profile,RadialQuotient.profileD,
    Nat.cast_zero,zero_add,pow_one,one_mul]
  field_simp [hsc]
  linear_combination (s : ℂ)^4*hw

theorem matching_coefficients (l : ℕ) (k : ℂ) (hk : k ≠ 0) (s : ℝ) (hs : 0 < s)
    (a b P : ℂ)
    (hc : b*outerProfile l k s=a*innerProfile l k s)
    (hj : (s : ℂ)^(l+2)*(b*deriv (outerProfile l k) s-a*deriv (innerProfile l k) s)= -P) :
    a=I*P*outerProfile l k s/(k*(s : ℂ)^l) ∧
      b=I*P*innerProfile l k s/(k*(s : ℂ)^l) := by
  let ip := innerProfile l k s
  let op := outerProfile l k s
  let idp := deriv (innerProfile l k) s
  let odp := deriv (outerProfile l k) s
  have hw := profile_wronskian l k hk s hs
  change ip*odp-op*idp=I*k/(s : ℂ)^2 at hw
  change b*op=a*ip at hc
  change (s : ℂ)^(l+2)*(b*odp-a*idp)= -P at hj
  have hsc : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hpow : (s : ℂ)^(l+2)=(s : ℂ)^l*(s : ℂ)^2 := pow_add _ _ _
  have hw' : (s : ℂ)^2*(ip*odp-op*idp)=I*k := by
    have h := (eq_div_iff (pow_ne_zero _ hsc)).mp hw
    linear_combination h
  have ha : a*(I*k)*(s : ℂ)^l= -P*op := by
    rw [hpow] at hj
    linear_combination op*hj-(s : ℂ)^l*(s : ℂ)^2*odp*hc-a*(s : ℂ)^l*hw'
  have hb : b*(I*k)*(s : ℂ)^l= -P*ip := by
    rw [hpow] at hj
    linear_combination ip*hj-(s : ℂ)^l*(s : ℂ)^2*idp*hc-b*(s : ℂ)^l*hw'
  constructor
  · apply (eq_div_iff (mul_ne_zero hk (pow_ne_zero _ hsc))).mpr
    change a*(k*(s : ℂ)^l)=I*P*op
    linear_combination -I*ha+a*k*(s : ℂ)^l*Complex.I_sq
  · apply (eq_div_iff (mul_ne_zero hk (pow_ne_zero _ hsc))).mpr
    change b*(k*(s : ℂ)^l)=I*P*ip
    linear_combination -I*hb+b*k*(s : ℂ)^l*Complex.I_sq


theorem coefficient_formula (k : ℝ) (hk : 0 < k) (y : Space) (hy : y ≠ 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖) :
    coefficient k y p r=I*complexEvaluate p y/((k : ℂ)*(‖y‖ : ℂ)^l)*
      innerProfile l (k : ℂ) (min r ‖y‖)*outerProfile l (k : ℂ) (max r ‖y‖) := by
  obtain ⟨a,b,ha,hb,hc,hj⟩ := source_matching k hk y hy p l hp hh
  obtain ⟨hea,heb⟩ := matching_coefficients l (k : ℂ) (ofReal_ne_zero.mpr hk.ne')
    ‖y‖ (norm_pos_iff.mpr hy) a b (complexEvaluate p y) hc hj
  rcases lt_or_gt_of_ne hry with hlt | hgt
  · rw [ha r ⟨hr,hlt⟩,hea,min_eq_left hlt.le,max_eq_right hlt.le]
    ring
  · rw [hb r hgt,heb,min_eq_right hgt.le,max_eq_left hgt.le]
    ring

end OQ14.ScalarGreenNormalization

#print axioms OQ14.ScalarGreenNormalization.profile_wronskian

#print axioms OQ14.ScalarGreenNormalization.matching_coefficients

#print axioms OQ14.ScalarGreenNormalization.coefficient_formula
