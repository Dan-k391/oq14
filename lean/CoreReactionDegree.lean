import BackgroundFluxMajorant
import HankelExteriorBounds

/-! Uniform degree majorant of the shell reaction coefficient against the regular Riccati-Bessel state.

For a layered stack with inner radius `R` the reaction multiplier of degree `l` is `gamma_l + I`.  Against the
regular state `(regular l s, regularD l s)` at every radius `s` with `rho0 <= s <= R`, and the source-side
factor `amplitude l 0 * b0^l`, the product has a geometric majorant `C (l+1) (1/2)^l` independent of the stack
radius, the stack thickness bound being fixed.  Three degree ranges: below the turning point of the radius
(`gamma` bounded), the window (`gamma` of exponential size in the degree, beaten by the outgoing geometric
bound), and the barrier range (the stack reaction against two regular values, Cauchy-Schwarz). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreReactionDegree
open Complex OQ14.RadialStack OQ14.HankelRealBasis
open OQ14.HankelEnergy (angular)

theorem abs_regular_le_norm (l : ℕ) (s : ℝ) : |regular l s| ≤ ‖OQ14.ModalAlgebra.xi l (s : ℂ)‖ :=
  Complex.abs_re_le_norm _

theorem abs_regularD_le_norm (l : ℕ) (s : ℝ) : |regularD l s| ≤ ‖OQ14.ModalAlgebra.xiD l (s : ℂ)‖ :=
  Complex.abs_re_le_norm _

/-- The regular state is dominated by the outgoing geometric bound at every radius beyond `rho0`. -/
theorem regular_state_geometric (l : ℕ) (B0 ρ0 s : ℝ) (hB0 : 0 ≤ B0) (hρ1 : 1 ≤ ρ0) (h2 : 2*B0 ≤ ρ0)
    (hs : ρ0 ≤ s) :
    RiccatiSeriesCoefficients.amplitude l 0 * B0^l * (|regular l s| + |regularD l s|) ≤
      2 * Real.exp ρ0 * (1/2 : ℝ)^l := by
  have h := HankelExteriorBounds.regular_outgoing_geometric l B0 ρ0 s hB0 hρ1 h2 hs
  have hA := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
  have hP : 0 ≤ RiccatiSeriesCoefficients.amplitude l 0 * B0^l := mul_nonneg hA (pow_nonneg hB0 l)
  calc RiccatiSeriesCoefficients.amplitude l 0 * B0^l * (|regular l s| + |regularD l s|)
      = RiccatiSeriesCoefficients.amplitude l 0 * B0^l * |regular l s| +
        RiccatiSeriesCoefficients.amplitude l 0 * B0^l * |regularD l s| := by ring
    _ ≤ RiccatiSeriesCoefficients.amplitude l 0 * B0^l * ‖OQ14.ModalAlgebra.xi l (s : ℂ)‖ +
        RiccatiSeriesCoefficients.amplitude l 0 * B0^l * ‖OQ14.ModalAlgebra.xiD l (s : ℂ)‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (abs_regular_le_norm l s) hP)
        (mul_le_mul_of_nonneg_left (abs_regularD_le_norm l s) hP)
    _ ≤ Real.exp ρ0 * (1/2 : ℝ)^l + Real.exp ρ0 * (1/2 : ℝ)^l := add_le_add h.1 h.2
    _ = 2 * Real.exp ρ0 * (1/2 : ℝ)^l := by ring

/-- The barrier range: the reaction coefficient against the regular state at `s`, weighted by the source-side
factor, has the geometric majorant. -/
theorem barrier_degree_bound (q b0 ρ0 : ℝ) (hq : 1 ≤ q) (hb0 : 0 < b0) (hρ1 : 1 ≤ ρ0)
    (l : ℕ) (gs : List Layer) (X R : ℝ) (hc : Chain gs X R) (hR0 : 0 < R)
    (hqp : ∀ g ∈ gs, g.q ≤ q) (hX : X ≤ 2*R) (hR : 2*Real.exp (3/4)*b0 ≤ R)
    (s : ℝ) (hs : ρ0 ≤ s) (hsR : s ≤ R) (hl : 2*q*R ≤ (l : ℝ)) :
    RiccatiSeriesCoefficients.amplitude l 0 * b0^l * ‖RadialSource.gamma l gs R X hR0‖ *
        (|regular l s| + |regularD l s|) ≤
      (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) * (1/2 : ℝ)^l := by
  have hs0 : 0 < s := by linarith
  have hexp34 : 1 ≤ Real.exp (3/4) := Real.one_le_exp (by norm_num)
  have hb0R : b0 ≤ R := by nlinarith
  have h2R : 2*R ≤ (l : ℝ) := by nlinarith
  have hν := RadialHighOrderBound.high_order_barrier l R hR0 h2R
  have hHs := RadialStackHighTail.actual_reaction_bound l hc q s hq hR0 hX hqp hs0 hsR hl
  have hHb := RadialStackHighTail.actual_reaction_bound l hc q b0 hq hR0 hX hqp hb0 hb0R hl
  obtain ⟨hpos_s, hpos_sD⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR0 hν s ⟨hs0, hsR⟩
  obtain ⟨hpos_b, -⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR0 hν b0 ⟨hb0, hb0R⟩
  have hlog := OQ14.RiccatiLogDerivative.barrier_logDerivative_bounds l R hR0 hν s ⟨hs0, hsR⟩
  have hgam1 := OQ14.RiccatiLogDerivative.gamma_ge_one l R hν
  have hgauss := OQ14.RiccatiGaussianBound.regular_gaussian_lower l R hR0 hν b0 ⟨hb0, hb0R⟩
  set g := ‖RadialSource.gamma l gs R X hR0‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  set A := RiccatiSeriesCoefficients.amplitude l 0 with hA
  have hApos : 0 < A := RiccatiSeriesCoefficients.amplitude_pos l 0
  set ψb := regular l b0 with hψb
  set ψs := regular l s with hψs
  -- derivative of the regular function against its value
  have hψD : |regularD l s| ≤ ((l : ℝ)+1)/ρ0 * ψs := by
    have h1 : s * regularD l s / ψs ≤ (l : ℝ)+1 := hlog.2
    have h2 : regularD l s ≤ ((l : ℝ)+1) * ψs / s := by
      rw [le_div_iff₀ hs0]
      have := (div_le_iff₀ hpos_s).mp h1
      linarith
    have h3 : ((l : ℝ)+1) * ψs / s ≤ ((l : ℝ)+1)/ρ0 * ψs := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hs0 (by linarith)]
      have : 0 ≤ ((l : ℝ)+1) * ψs := by positivity
      nlinarith
    rw [abs_of_pos hpos_sD]
    exact h2.trans h3
  -- Cauchy-Schwarz for the reaction against the two regular values
  have hCS : g * ψb * ψs ≤ 4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) / (((2*l+1 : ℝ)) * R^(2*l+1)) := by
    have hsq : (g * ψb * ψs)^2 ≤ (4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) /
        (((2*l+1 : ℝ)) * R^(2*l+1)))^2 := by
      have e1 : (g * ψb * ψs)^2 = (g * ψb^2) * (g * ψs^2) := by ring
      have hp1 : 0 ≤ g * ψb^2 := by positivity
      have hp2 : 0 ≤ g * ψs^2 := by positivity
      rw [e1]
      calc (g * ψb^2) * (g * ψs^2)
          ≤ (4*Real.exp (3*R/2)*b0^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1))) *
            (4*Real.exp (3*R/2)*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1))) :=
            mul_le_mul hHb hHs hp2 (by positivity)
        _ = (4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) / (((2*l+1 : ℝ)) * R^(2*l+1)))^2 := by
            have e2 : b0^(2*l+2) = (b0^(l+1))^2 := by rw [← pow_mul]; ring_nf
            have e3 : s^(2*l+2) = (s^(l+1))^2 := by rw [← pow_mul]; ring_nf
            rw [e2, e3]
            field_simp
            ring
    have hY : 0 ≤ 4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) / (((2*l+1 : ℝ)) * R^(2*l+1)) := by positivity
    have hX0 : 0 ≤ g * ψb * ψs := by positivity
    by_contra hcon
    push_neg at hcon
    nlinarith
  -- convert the source-side factor to the regular value at b0
  have hamp : A * b0^l ≤ ψb * Real.exp (b0^2/6) / b0 := by
    have hlow : A * b0^(l+1) * Real.exp (-b0^2/6) ≤ ψb := by
      refine le_trans ?_ hgauss
      have hden : (6 : ℝ) ≤ 2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2) := by
        have := Nat.cast_nonneg (α := ℝ) l
        linarith
      have hexp : Real.exp (-b0^2/6) ≤
          Real.exp (-b0^2/(2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2))) := by
        apply Real.exp_le_exp.mpr
        have hpos : 0 < 2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2) := by linarith
        have : b0^2/(2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2)) ≤ b0^2/6 :=
          div_le_div_of_nonneg_left (sq_nonneg b0) (by norm_num) hden
        have e4 : -b0^2/6 = -(b0^2/6) := by ring
        have e5 : -b0^2/(2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2)) =
            -(b0^2/(2*(((l : ℝ)) + OQ14.RiccatiLogDerivative.gamma l R + 2))) := by ring
        rw [e4, e5]
        linarith
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    rw [le_div_iff₀ hb0]
    have hep : 0 < Real.exp (b0^2/6) := Real.exp_pos _
    have : A * b0^(l+1) = (A * b0^l) * b0 := by ring
    have h6 : Real.exp (-b0^2/6) * Real.exp (b0^2/6) = 1 := by
      rw [← Real.exp_add]
      have : -b0^2/6 + b0^2/6 = 0 := by ring
      rw [this, Real.exp_zero]
    calc A * b0^l * b0 = (A * b0^(l+1)) * (Real.exp (-b0^2/6) * Real.exp (b0^2/6)) := by
          rw [h6]; ring
      _ = (A * b0^(l+1) * Real.exp (-b0^2/6)) * Real.exp (b0^2/6) := by ring
      _ ≤ ψb * Real.exp (b0^2/6) := mul_le_mul_of_nonneg_right hlow hep.le
  have hmain : A * b0^l * g * ψs ≤ 4 * Real.exp (b0^2/6) * (1/2 : ℝ)^l := by
    have step1 : A * b0^l * g * ψs ≤ (Real.exp (b0^2/6) / b0) * (g * ψb * ψs) := by
      have hh := mul_le_mul_of_nonneg_right hamp (by positivity : 0 ≤ g * ψs)
      calc A * b0^l * g * ψs = (A * b0^l) * (g * ψs) := by ring
        _ ≤ (ψb * Real.exp (b0^2/6) / b0) * (g * ψs) := hh
        _ = (Real.exp (b0^2/6) / b0) * (g * ψb * ψs) := by ring
    have step2 : (Real.exp (b0^2/6) / b0) * (g * ψb * ψs) ≤
        (Real.exp (b0^2/6) / b0) * (4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) /
          (((2*l+1 : ℝ)) * R^(2*l+1))) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    have step3 : (Real.exp (b0^2/6) / b0) * (4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) /
        (((2*l+1 : ℝ)) * R^(2*l+1))) ≤ 4 * Real.exp (b0^2/6) * Real.exp (3*R/2) * (b0/R)^l := by
      have hsR1 : s^(l+1) ≤ R^(l+1) := pow_le_pow_left₀ hs0.le hsR _
      have e6 : R^(2*l+1) = R^l * R^(l+1) := by rw [← pow_add]; ring_nf
      have e7 : (b0/R)^l = b0^l / R^l := div_pow _ _ _
      have hRl : 0 < R^l := pow_pos hR0 l
      have hRl1 : 0 < R^(l+1) := pow_pos hR0 (l+1)
      have hl1 : (1 : ℝ) ≤ 2*l+1 := by
        have := Nat.cast_nonneg (α := ℝ) l
        linarith
      calc (Real.exp (b0^2/6) / b0) * (4 * Real.exp (3*R/2) * (b0^(l+1) * s^(l+1)) /
            (((2*l+1 : ℝ)) * R^(2*l+1)))
          = 4 * Real.exp (b0^2/6) * Real.exp (3*R/2) * (b0^l * s^(l+1)) /
            ((2*l+1 : ℝ) * (R^l * R^(l+1))) := by
            rw [e6]
            field_simp
            ring
        _ ≤ 4 * Real.exp (b0^2/6) * Real.exp (3*R/2) * (b0^l * R^(l+1)) /
            (1 * (R^l * R^(l+1))) := by
            apply div_le_div₀ (by positivity) _ (by positivity) _
            · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsR1 (pow_nonneg hb0.le _))
                (by positivity)
            · exact mul_le_mul hl1 le_rfl (by positivity) (by positivity)
        _ = 4 * Real.exp (b0^2/6) * Real.exp (3*R/2) * (b0/R)^l := by
            rw [e7]
            field_simp
            ring
    have step4 : Real.exp (3*R/2) * (b0/R)^l ≤ (1/2 : ℝ)^l := by
      have hRl2 : R ≤ (l : ℝ)/2 := by linarith
      have e8 : Real.exp (3*R/2) ≤ Real.exp (3/4) ^ l := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        linarith
      have e9 : Real.exp (3/4) * (b0/R) ≤ 1/2 := by
        rw [mul_div_assoc', div_le_iff₀ hR0]
        nlinarith
      calc Real.exp (3*R/2) * (b0/R)^l ≤ Real.exp (3/4)^l * (b0/R)^l :=
            mul_le_mul_of_nonneg_right e8 (by positivity)
        _ = (Real.exp (3/4) * (b0/R))^l := (mul_pow _ _ _).symm
        _ ≤ (1/2 : ℝ)^l := pow_le_pow_left₀ (by positivity) e9 l
    calc A * b0^l * g * ψs ≤ 4 * Real.exp (b0^2/6) * Real.exp (3*R/2) * (b0/R)^l := step1.trans (step2.trans step3)
      _ = 4 * Real.exp (b0^2/6) * (Real.exp (3*R/2) * (b0/R)^l) := by ring
      _ ≤ 4 * Real.exp (b0^2/6) * (1/2 : ℝ)^l := mul_le_mul_of_nonneg_left step4 (by positivity)
  have habs : |regular l s| = ψs := abs_of_pos hpos_s
  rw [habs]
  calc A * b0^l * g * (ψs + |regularD l s|) = A * b0^l * g * ψs + A * b0^l * g * |regularD l s| := by ring
    _ ≤ A * b0^l * g * ψs + A * b0^l * g * (((l : ℝ)+1)/ρ0 * ψs) := by
        gcongr
    _ = (1 + ((l : ℝ)+1)/ρ0) * (A * b0^l * g * ψs) := by ring
    _ ≤ (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6) * (1/2 : ℝ)^l) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) * (1/2 : ℝ)^l := by ring

/-- **Uniform degree majorant of the reaction coefficient.**  For stacks with parameters bounded by `q`, `M`,
thickness bound `d`, outer radius at most twice the inner radius `R`, and `R` at least `max rho0 (2 e^{3/4} b0)`,
the reaction multiplier `gamma + I` against the regular state at every radius `s ∈ [rho0, R]`, weighted by the
source-side factor `amplitude l 0 * b0^l`, is at most `C (l+1) (1/2)^l` with `C` depending only on
`(q, M, d, b0, rho0)`. -/
theorem reaction_degree_bound (q M d b0 ρ0 : ℝ) (hq : 1 ≤ q) (hM : 1 ≤ M) (hb0 : 0 < b0) (hρ1 : 1 ≤ ρ0)
    (hρ0 : 2 * (b0 * Real.exp (8 * HankelIntermediateBounds.exponent q)) ≤ ρ0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℕ) (gs : List Layer) (X R : ℝ) (_hc : Chain gs X R) (hR0 : 0 < R)
      (_hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (_hqp : ∀ g ∈ gs, g.q ≤ q)
      (_hX : X ≤ 2*R) (_hd : X - R ≤ d) (_hR : max ρ0 (2*Real.exp (3/4)*b0) ≤ R)
      (s : ℝ) (_hs : ρ0 ≤ s) (_hsR : s ≤ R),
      RiccatiSeriesCoefficients.amplitude l 0 * b0^l * ‖RadialSource.gamma l gs R X hR0 + Complex.I‖ *
        (|regular l s| + |regularD l s|) ≤ C * ((l : ℝ)+1) * (1/2 : ℝ)^l := by
  have hE1 : 0 ≤ HankelIntermediateBounds.exponent q := RadialMiddleTail.exponent_nonnegative q hq
  have hM0 : 0 ≤ M := by linarith
  have hAq : 0 ≤ RadialIntermediateBound.angularBound q := by
    dsimp [RadialIntermediateBound.angularBound]
    positivity
  set E1 := HankelIntermediateBounds.exponent q with hE1def
  set E8 := Real.exp (8 * E1) with hE8def
  set CL : ℝ := (4/(1-(1/2 : ℝ)^2))^2 * Real.exp ((2*M+(1/2 : ℝ)^2)*d) with hCL
  set CW : ℝ := (RadialIntermediateBound.frameConstant q)^2 *
    Real.exp ((2*M+RadialIntermediateBound.angularBound q)*d) * E8 with hCW
  set Cg : ℝ := max CL CW with hCg
  have hCL0 : 0 ≤ CL := by positivity
  have hCW0 : 0 ≤ CW := by positivity
  have hCg0 : 0 ≤ Cg := le_max_of_le_left hCL0
  refine ⟨2 * Real.exp ρ0 * (1 + Cg) + 4 * Real.exp (b0^2/6) * (1 + 1/ρ0), by positivity, ?_⟩
  intro l gs X R hc hR0 hp hqp hX hd hR s hs hsR
  have hρpos : 0 < ρ0 := by linarith
  have hRρ : ρ0 ≤ R := le_trans (le_max_left _ _) hR
  have hRb : 2*Real.exp (3/4)*b0 ≤ R := le_trans (le_max_right _ _) hR
  have hR1 : 1 ≤ R := hρ1.trans hRρ
  have hE8one : 1 ≤ E8 := Real.one_le_exp (by positivity)
  have hApos : 0 < RiccatiSeriesCoefficients.amplitude l 0 := RiccatiSeriesCoefficients.amplitude_pos l 0
  set A := RiccatiSeriesCoefficients.amplitude l 0 with hAdef
  set S := |regular l s| + |regularD l s| with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hP0 : 0 ≤ A * b0^l := by positivity
  have hb02 : 2*b0 ≤ ρ0 := by nlinarith
  have hsecond : A * b0^l * S ≤ 2 * Real.exp ρ0 * (1/2 : ℝ)^l :=
    regular_state_geometric l b0 ρ0 s hb0.le hρ1 hb02 hs
  have hhalf : 0 ≤ (1/2 : ℝ)^l := by positivity
  have hexp0 : 0 < Real.exp ρ0 := Real.exp_pos _
  have hg0 : 0 ≤ ‖RadialSource.gamma l gs R X hR0‖ := norm_nonneg _
  -- the bound for a gamma controlled by a constant times a geometric-friendly power
  have hfirst : A * b0^l * ‖RadialSource.gamma l gs R X hR0‖ * S ≤
      (2 * Real.exp ρ0 * Cg + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l := by
    by_cases hA : angular l ≤ (1/2 : ℝ)^2 * R^2
    · have hγ := RadialSource.gamma_low_range l hc M (1/2) hR0 (by norm_num) hA hp
      have hγ' : ‖RadialSource.gamma l gs R X hR0‖ ≤ Cg := by
        refine hγ.trans ((le_max_left CL CW).trans' ?_)
        rw [hCL]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hd (by positivity)
      calc A * b0^l * ‖RadialSource.gamma l gs R X hR0‖ * S
          ≤ A * b0^l * Cg * S := by gcongr
        _ = Cg * (A * b0^l * S) := by ring
        _ ≤ Cg * (2 * Real.exp ρ0 * (1/2 : ℝ)^l) := mul_le_mul_of_nonneg_left hsecond hCg0
        _ ≤ (2 * Real.exp ρ0 * Cg + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l := by
            have : 0 ≤ (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) * (1/2 : ℝ)^l := by positivity
            nlinarith
    · by_cases hB : (l : ℝ) ≤ 2*q*R
      · have hRl : R < 2*((l : ℝ)+1) := by
          by_contra hcon
          push_neg at hcon
          apply hA
          unfold angular
          nlinarith [Nat.cast_nonneg (α := ℝ) l]
        have hw := RadialIntermediateBound.actual_gamma_window_bound l hc q M d hq hM0 hR1 hX hd hB hp
        have hexpR : Real.exp (4*E1*R) ≤ E8^(l+1) := by
          rw [hE8def, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hRl.le (by positivity : 0 ≤ 4*E1)]
        have hγ : ‖RadialSource.gamma l gs R X hR0‖ ≤ CW * E8^l := by
          refine hw.trans ?_
          rw [Real.exp_add, hCW]
          have e1 : E8^(l+1) = E8^l * E8 := pow_succ _ _
          calc (RadialIntermediateBound.frameConstant q)^2 *
                (Real.exp (4*E1*R) * Real.exp ((2*M+RadialIntermediateBound.angularBound q)*d))
              ≤ (RadialIntermediateBound.frameConstant q)^2 *
                (E8^(l+1) * Real.exp ((2*M+RadialIntermediateBound.angularBound q)*d)) := by gcongr
            _ = (RadialIntermediateBound.frameConstant q)^2 *
                Real.exp ((2*M+RadialIntermediateBound.angularBound q)*d) * E8 * E8^l := by
                rw [e1]; ring
        have hgeo := regular_state_geometric l (b0*E8) ρ0 s (by positivity) hρ1 (by linarith) hs
        have hmul : (b0*E8)^l = b0^l * E8^l := mul_pow _ _ _
        calc A * b0^l * ‖RadialSource.gamma l gs R X hR0‖ * S
            ≤ A * b0^l * (CW * E8^l) * S := by gcongr
          _ = CW * (A * (b0*E8)^l * S) := by rw [hmul]; ring
          _ ≤ CW * (2 * Real.exp ρ0 * (1/2 : ℝ)^l) := mul_le_mul_of_nonneg_left hgeo hCW0
          _ ≤ Cg * (2 * Real.exp ρ0 * (1/2 : ℝ)^l) :=
              mul_le_mul_of_nonneg_right (le_max_right CL CW) (by positivity)
          _ ≤ (2 * Real.exp ρ0 * Cg + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l := by
              have : 0 ≤ (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) * (1/2 : ℝ)^l := by positivity
              nlinarith
      · have hl' : 2*q*R ≤ (l : ℝ) := le_of_lt (not_le.mp hB)
        have hbar := barrier_degree_bound q b0 ρ0 hq hb0 hρ1 l gs X R hc hR0 hqp hX hRb s hs hsR hl'
        calc A * b0^l * ‖RadialSource.gamma l gs R X hR0‖ * S
            ≤ (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) * (1/2 : ℝ)^l := hbar
          _ ≤ (2 * Real.exp ρ0 * Cg + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l := by
              have : 0 ≤ 2 * Real.exp ρ0 * Cg * (1/2 : ℝ)^l := by positivity
              nlinarith
  have htri : ‖RadialSource.gamma l gs R X hR0 + Complex.I‖ ≤ ‖RadialSource.gamma l gs R X hR0‖ + 1 :=
    (norm_add_le _ _).trans (by simp)
  have hl1 : (1 : ℝ) ≤ (l : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) l
    linarith
  have hfrac : 0 ≤ ((l : ℝ)+1)/ρ0 := by positivity
  calc A * b0^l * ‖RadialSource.gamma l gs R X hR0 + Complex.I‖ * S
      ≤ A * b0^l * (‖RadialSource.gamma l gs R X hR0‖ + 1) * S := by gcongr
    _ = A * b0^l * ‖RadialSource.gamma l gs R X hR0‖ * S + A * b0^l * S := by ring
    _ ≤ (2 * Real.exp ρ0 * Cg + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l +
        2 * Real.exp ρ0 * (1/2 : ℝ)^l := add_le_add hfirst hsecond
    _ = (2 * Real.exp ρ0 * (1 + Cg) + (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6))) * (1/2 : ℝ)^l := by ring
    _ ≤ (2 * Real.exp ρ0 * (1 + Cg) + 4 * Real.exp (b0^2/6) * (1 + 1/ρ0)) * ((l : ℝ)+1) * (1/2 : ℝ)^l := by
        apply mul_le_mul_of_nonneg_right _ hhalf
        have h1 : 2 * Real.exp ρ0 * (1 + Cg) ≤ 2 * Real.exp ρ0 * (1 + Cg) * ((l : ℝ)+1) :=
          le_mul_of_one_le_right (by positivity) hl1
        have h2 : (1 + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) ≤
            4 * Real.exp (b0^2/6) * (1 + 1/ρ0) * ((l : ℝ)+1) := by
          have e : 4 * Real.exp (b0^2/6) * (1 + 1/ρ0) * ((l : ℝ)+1) =
              (((l : ℝ)+1) + ((l : ℝ)+1)/ρ0) * (4 * Real.exp (b0^2/6)) := by ring
          rw [e]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        nlinarith

end OQ14.CoreReactionDegree

#print axioms OQ14.CoreReactionDegree.abs_regular_le_norm
#print axioms OQ14.CoreReactionDegree.abs_regularD_le_norm
#print axioms OQ14.CoreReactionDegree.regular_state_geometric
#print axioms OQ14.CoreReactionDegree.barrier_degree_bound
#print axioms OQ14.CoreReactionDegree.reaction_degree_bound
