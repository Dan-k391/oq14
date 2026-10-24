import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Cesaro (interval average) lemma for the unit throughput of the lossless sphere flux.

If a real function `f` is almost everywhere equal to a constant `P` beyond `R0`, and for `r > R0` it has the
far expansion `f r = g r + Re (exp (-2 i k r) * c r) + e r` with `g → G`, `c → C`, `e → 0`, then `P = G`.
The proof averages over `[R1, R1 + L]`: the oscillating term with the limit coefficient `C` has the explicit
antiderivative `(C.re sin (2 k r) - C.im cos (2 k r)) / (2 k)`, so its integral is bounded by
`(|C.re| + |C.im|) / |k|`, independently of `R1` and `L`; the three convergent remainders are at most `epsilon`
beyond some `R1`.  No pointwise Riemann-Lebesgue step is used, and no integrability of `f`, `g`, `c`, `e` is
needed (only that `f` is a.e. constant). -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ChannelCesaroThroughput
open MeasureTheory Filter Topology Set
open scoped Interval

/-- The oscillating term with constant coefficient `C`. -/
def osc (k : ℝ) (C : ℂ) (r : ℝ) : ℝ := C.re * Real.cos (2*k*r) + C.im * Real.sin (2*k*r)

theorem exp_mul_re (k r : ℝ) (c : ℂ) :
    (Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * c).re = osc k c r := by
  have h : -2 * (k : ℂ) * (r : ℂ) * Complex.I = ((-(2*k*r) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  unfold osc
  ring

theorem norm_exp_osc (k r : ℝ) : ‖Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I)‖ = 1 := by
  have h : -2 * (k : ℂ) * (r : ℂ) * Complex.I = ((-(2*k*r) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

theorem osc_continuous (k : ℝ) (C : ℂ) : Continuous (osc k C) := by
  unfold osc
  fun_prop

/-- The interval integral of the oscillating term is bounded independently of the interval. -/
theorem osc_integral_bound (k : ℝ) (hk : k ≠ 0) (C : ℂ) (a b : ℝ) :
    |∫ r in a..b, osc k C r| ≤ (|C.re| + |C.im|) / |k| := by
  let F : ℝ → ℝ := fun r => (C.re * Real.sin (2*k*r) - C.im * Real.cos (2*k*r)) / (2*k)
  have hd : ∀ x ∈ uIcc a b, HasDerivAt F (osc k C x) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => 2*k*r) (2*k) x := by
      simpa using (hasDerivAt_id x).const_mul (2*k)
    have h2 := (h1.sin.const_mul C.re).sub (h1.cos.const_mul C.im)
    have h3 := h2.div_const (2*k)
    convert h3 using 1
    unfold osc
    field_simp
    ring
  have hi : IntervalIntegrable (osc k C) volume a b := (osc_continuous k C).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have hk2 : 0 < |2*k| := abs_pos.mpr (mul_ne_zero two_ne_zero hk)
  have hF : ∀ r, |F r| ≤ (|C.re| + |C.im|) / (2*|k|) := by
    intro r
    have hs := Real.abs_sin_le_one (2*k*r)
    have hc := Real.abs_cos_le_one (2*k*r)
    have hnum : |C.re * Real.sin (2*k*r) - C.im * Real.cos (2*k*r)| ≤ |C.re| + |C.im| := by
      calc _ ≤ |C.re * Real.sin (2*k*r)| + |C.im * Real.cos (2*k*r)| := abs_sub _ _
        _ = |C.re| * |Real.sin (2*k*r)| + |C.im| * |Real.cos (2*k*r)| := by rw [abs_mul, abs_mul]
        _ ≤ |C.re| * 1 + |C.im| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
        _ = _ := by ring
    have h2k : |2*k| = 2*|k| := by rw [abs_mul, abs_two]
    show |(C.re * Real.sin (2*k*r) - C.im * Real.cos (2*k*r)) / (2*k)| ≤ _
    rw [abs_div, h2k]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  calc |F b - F a| ≤ |F b| + |F a| := abs_sub _ _
    _ ≤ (|C.re| + |C.im|) / (2*|k|) + (|C.re| + |C.im|) / (2*|k|) := add_le_add (hF b) (hF a)
    _ = (|C.re| + |C.im|) / |k| := by
        have : |k| ≠ 0 := abs_ne_zero.mpr hk
        field_simp
        ring

/-- Cesaro lemma: an a.e. constant function with the oscillating far expansion has the constant equal to the
limit of its non-oscillating part. -/
theorem cesaro_constant_limit (f g e : ℝ → ℝ) (c : ℝ → ℂ) (P G : ℝ) (C : ℂ) (k R0 : ℝ) (hk : k ≠ 0)
    (hP : ∀ᵐ r ∂(volume.restrict (Ioi R0)), f r = P)
    (hexp : ∀ r, R0 < r →
      f r = g r + (Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * c r).re + e r)
    (hg : Tendsto g atTop (𝓝 G)) (hc : Tendsto c atTop (𝓝 C)) (he : Tendsto e atTop (𝓝 0)) :
    P = G := by
  have hbound : ∀ ε : ℝ, 0 < ε → |P - G| ≤ 2*ε := by
    intro ε hε
    have hε3 : 0 < ε/3 := by positivity
    have h1 := (hg.eventually (Metric.closedBall_mem_nhds G hε3))
    have h2 := (hc.eventually (Metric.closedBall_mem_nhds C hε3))
    have h3 := (he.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hε3))
    obtain ⟨R1, hR1⟩ := eventually_atTop.mp (h1.and (h2.and (h3.and (eventually_gt_atTop R0))))
    let R2 : ℝ := max R1 (R0 + 1)
    have hR2 : ∀ r, R2 ≤ r → |g r - G| ≤ ε/3 ∧ ‖c r - C‖ ≤ ε/3 ∧ |e r| ≤ ε/3 ∧ R0 < r := by
      intro r hr
      have hr1 : R1 ≤ r := (le_max_left _ _).trans hr
      obtain ⟨a1, a2, a3, a4⟩ := hR1 r hr1
      refine ⟨?_, ?_, ?_, a4⟩
      · simpa [Real.dist_eq, abs_sub_comm] using a1
      · simpa [dist_eq_norm] using a2
      · simpa [Real.dist_eq] using a3
    -- pointwise bound of the remainder beyond R2
    have hpt : ∀ r, R2 ≤ r → f r - G - osc k C r ≤ ε ∧ -(f r - G - osc k C r) ≤ ε := by
      intro r hr
      obtain ⟨a1, a2, a3, a4⟩ := hR2 r hr
      have hf := hexp r a4
      have hcn : |(Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * (c r - C)).re| ≤ ε/3 := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_exp_osc, one_mul]
        exact a2
      have hsplit : (Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * c r).re - osc k C r =
          (Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * (c r - C)).re := by
        rw [← exp_mul_re k r C, mul_sub, Complex.sub_re]
      have hd : f r - G - osc k C r = (g r - G) + (Complex.exp (-2 * (k : ℂ) * (r : ℂ) * Complex.I) * (c r - C)).re + e r := by
        rw [hf, ← hsplit]
        ring
      rw [hd]
      have := abs_le.mp a1
      have := abs_le.mp hcn
      have := abs_le.mp a3
      constructor <;> linarith
    -- the averaged identity on [R2, R2 + L]
    have hL : ∀ L : ℝ, 0 < L → |P - G| * L ≤ ε * L + (|C.re| + |C.im|) / |k| := by
      intro L hL
      have hab : R2 ≤ R2 + L := by linarith
      have hmeas : MeasurableSet (Ioi R0) := measurableSet_Ioi
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi R0 → f x = P := (ae_restrict_iff' hmeas).mp hP
      -- a.e. bound of the continuous function P - G - osc on the interval
      have hq : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι R2 (R2 + L) → ‖P - G - osc k C x‖ ≤ ε := by
        filter_upwards [hae] with x hx hxI
        rw [uIoc_of_le hab] at hxI
        have hxR : R2 ≤ x := hxI.1.le
        have hx0 : R0 < x := (hR2 x hxR).2.2.2
        have hfx := hx hx0
        have := hpt x hxR
        rw [hfx] at this
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2]
      have hn := intervalIntegral.norm_integral_le_of_norm_le_const_ae hq
      have hcalc : ∫ x in R2..(R2 + L), (P - G - osc k C x) = (P - G) * L - ∫ x in R2..(R2 + L), osc k C x := by
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          ((osc_continuous k C).intervalIntegrable _ _)]
        simp
        ring
      rw [hcalc, add_sub_cancel_left, abs_of_pos hL, Real.norm_eq_abs] at hn
      have hos := osc_integral_bound k hk C R2 (R2 + L)
      have h4 : |P - G| * L = |(P - G) * L| := by rw [abs_mul, abs_of_pos hL]
      rw [h4]
      calc |(P - G) * L| = |((P - G) * L - ∫ x in R2..(R2 + L), osc k C x) + ∫ x in R2..(R2 + L), osc k C x| := by ring_nf
        _ ≤ |(P - G) * L - ∫ x in R2..(R2 + L), osc k C x| + |∫ x in R2..(R2 + L), osc k C x| := abs_add _ _
        _ ≤ ε * L + (|C.re| + |C.im|) / |k| := add_le_add hn hos
    -- choose L
    have hK0 : 0 ≤ (|C.re| + |C.im|) / |k| := by positivity
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (|C.re| + |C.im|) / |k| := ⟨_, rfl⟩
    rw [← hK] at hL hK0
    have hLpos : 0 < (K + 1) / ε := by positivity
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (K + 1) / ε := ⟨_, rfl⟩
    rw [← hLdef] at hLpos
    have hεL : ε * L = K + 1 := by
      rw [hLdef]
      field_simp
    have h5 := hL L hLpos
    have h8 : |P - G| * L ≤ (2 * ε) * L := by nlinarith
    exact le_of_mul_le_mul_right h8 hLpos
  rcases eq_or_ne P G with hPG | hne
  · exact hPG
  · exfalso
    have hpos : 0 < |P - G| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h9 := hbound (|P - G| / 4) (by positivity)
    linarith

end OQ14.ChannelCesaroThroughput
#print axioms OQ14.ChannelCesaroThroughput.exp_mul_re
#print axioms OQ14.ChannelCesaroThroughput.norm_exp_osc
#print axioms OQ14.ChannelCesaroThroughput.osc_continuous
#print axioms OQ14.ChannelCesaroThroughput.osc_integral_bound
#print axioms OQ14.ChannelCesaroThroughput.cesaro_constant_limit
