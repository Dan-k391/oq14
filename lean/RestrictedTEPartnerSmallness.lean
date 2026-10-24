import WeightedRemainderSchur
import RestrictedTEPartnerSmall
import KernelEstimates
import SourcePairedNormSmallness
import SourcePairedSmallInclusion

/-! Smallness of the doubled (partner-ball) device in the finite-shell closure.

For the carrier consisting of `N` balls of radius `s = ρ a` the dynamic remainder kernel only has to be
integrated over the difference set, a finite union of balls of radius `2 s`.  The remainder kernel obeys
`‖remainder k z‖ ≤ (14 k² / (4 π)) ‖z‖⁻¹`, so the mass over a ball of radius `t` is at most `(35/3) k² t²`
independently of the centre.  With `WeightedRemainderSchur.weightedRemainder_norm_le_of_mass` this gives
`‖weightedRemainder (partnerCoefficient ..) 1 b‖ ≤ 9 χ N² (140/3) ρ² a²`, quadratic in the scale `a`; together
with the cubic carrier volume and the radius-independent kernel constant of `SourcePairedSmallInclusion`
the limiting effective inclusion block is a unit along the scales `a_n = (q^n)⁻¹` for large `n` (`q > 1`),
via `SourcePairedNormSmallness.limitEffective_isUnit_of_remainder_norm`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPartnerSmallness
open MeasureTheory Metric Set Filter Topology
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient

theorem volume_real_ball (z0 : Space) (t : ℝ) (ht : 0 ≤ t) :
    volume.real (ball z0 t) = t^3 * (Real.pi*4/3) := by
  simp only [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem ball_subset_closedBall_norm (z0 : Space) (t : ℝ) : ball z0 t ⊆ closedBall (0 : Space) (‖z0‖+t) := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  rw [mem_closedBall, dist_zero_right]
  have := norm_sub_norm_le z z0
  linarith

/-- The inverse-norm integral over a ball of any centre is at most `(5/2)(4π/3) t²`. -/
theorem inv_norm_ball_integral_le (z0 : Space) (t : ℝ) (ht : 0 < t) :
    ∫ z in ball z0 t, ‖z‖⁻¹ ≤ (5/2 : ℝ) * (Real.pi*4/3) * t^2 := by
  have hsub := ball_subset_closedBall_norm z0 t
  have hgi : IntegrableOn (fun z : Space => ‖z‖⁻¹) (ball z0 t) :=
    (KernelIntegrability.inverse_norm_integrable_ball (‖z0‖+t)).mono_set hsub
  have hI : Integrable ((closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹)) :=
    (KernelIntegrability.inverse_norm_integrable_ball t).integrable_indicator measurableSet_closedBall
  have hpt : ∀ z : Space, ‖z‖⁻¹ ≤ (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z + t⁻¹ := by
    intro z
    have ht0 : 0 ≤ t⁻¹ := by positivity
    by_cases hz : z ∈ closedBall (0 : Space) t
    · rw [Set.indicator_of_mem hz]
      linarith
    · rw [Set.indicator_of_not_mem hz, zero_add]
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact inv_anti₀ ht hz.le
  have hconst : IntegrableOn (fun _ : Space => t⁻¹) (ball z0 t) :=
    integrableOn_const.mpr (Or.inr measure_ball_lt_top)
  have h1 : ∫ z in ball z0 t, ‖z‖⁻¹ ≤
      ∫ z in ball z0 t, ((closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z + t⁻¹) :=
    setIntegral_mono hgi (hI.integrableOn.add hconst) hpt
  have h3 : ∫ z in ball z0 t, (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z ≤
      ∫ z, (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z :=
    setIntegral_le_integral hI (Eventually.of_forall (fun z =>
      Set.indicator_nonneg (fun z _ => by positivity) z))
  have hV1 : volume.real (ball (0 : Space) 1) = Real.pi*4/3 := by
    rw [volume_real_ball 0 1 zero_le_one]
    ring
  have h4 : ∫ z, (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z =
      (3/2 : ℝ) * (Real.pi*4/3) * t^2 := by
    rw [integral_indicator measurableSet_closedBall, KernelEstimates.inverse_norm_integral_ball t ht.le, hV1]
  have h5 : ∫ z in ball z0 t, t⁻¹ = t⁻¹ * (t^3 * (Real.pi*4/3)) := by
    rw [setIntegral_const, smul_eq_mul, volume_real_ball z0 t ht.le]
    ring
  calc ∫ z in ball z0 t, ‖z‖⁻¹
      ≤ ∫ z in ball z0 t, ((closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z + t⁻¹) := h1
    _ = (∫ z in ball z0 t, (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z) +
          ∫ z in ball z0 t, t⁻¹ := integral_add hI.integrableOn hconst
    _ ≤ (∫ z, (closedBall (0 : Space) t).indicator (fun z : Space => ‖z‖⁻¹) z) + ∫ z in ball z0 t, t⁻¹ :=
        add_le_add_right h3 _
    _ = (3/2 : ℝ) * (Real.pi*4/3) * t^2 + t⁻¹ * (t^3 * (Real.pi*4/3)) := by rw [h4, h5]
    _ = (5/2 : ℝ) * (Real.pi*4/3) * t^2 := by
        have ht0 : t ≠ 0 := ht.ne'
        field_simp
        ring

/-- The L1 mass of the dyadic remainder over a ball of any centre and radius `t` is at most `(35/3) k² t²`. -/
theorem remainder_ball_mass (k : ℝ) (z0 : Space) (t : ℝ) (i j : Fin 3) :
    ∫ z in ball z0 t, ‖DyadicKernel.remainder k z i j‖ ≤ (35/3 : ℝ) * k^2 * t^2 := by
  rcases le_or_lt t 0 with ht | ht
  · rw [Metric.ball_eq_empty.mpr ht]
    simp only [Measure.restrict_empty, integral_zero_measure]
    positivity
  · have hsub := ball_subset_closedBall_norm z0 t
    have hi : IntegrableOn (fun z : Space => DyadicKernel.remainder k z i j) (ball z0 t) :=
      (RealKernelBounds.remainder_integrable_ball k (‖z0‖+t) i j).mono_set hsub
    have hgi : IntegrableOn (fun z : Space => ‖z‖⁻¹) (ball z0 t) :=
      (KernelIntegrability.inverse_norm_integrable_ball (‖z0‖+t)).mono_set hsub
    calc ∫ z in ball z0 t, ‖DyadicKernel.remainder k z i j‖
        ≤ ∫ z in ball z0 t, (14*k^2/(4*Real.pi)) * ‖z‖⁻¹ :=
          setIntegral_mono hi.norm (hgi.const_mul _) (fun z => RealKernelBounds.remainder_bound_all k z i j)
      _ = (14*k^2/(4*Real.pi)) * ∫ z in ball z0 t, ‖z‖⁻¹ := integral_const_mul _ _
      _ ≤ (14*k^2/(4*Real.pi)) * ((5/2 : ℝ) * (Real.pi*4/3) * t^2) :=
          mul_le_mul_of_nonneg_left (inv_norm_ball_integral_le z0 t ht) (by positivity)
      _ = (35/3 : ℝ) * k^2 * t^2 := by
          have hp : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp
          ring

section Family
variable {κ : Type*} [Fintype κ]

/-- Union of balls containing every difference of two points of the union of balls `ball (c j) (r j)`. -/
def diffSet (c : κ → Space) (r : κ → ℝ) : Set Space :=
  ⋃ m : κ × κ, ball (c m.1 - c m.2) (r m.1 + r m.2)

theorem diffSet_measurable (c : κ → Space) (r : κ → ℝ) : MeasurableSet (diffSet c r) :=
  MeasurableSet.iUnion (fun _ => measurableSet_ball)

theorem diff_mem (c : κ → Space) (r : κ → ℝ) (x y : Space) (hx : x ∈ ⋃ j, ball (c j) (r j))
    (hy : y ∈ ⋃ j, ball (c j) (r j)) : x - y ∈ diffSet c r := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  obtain ⟨j', hj'⟩ := mem_iUnion.mp hy
  refine mem_iUnion.mpr ⟨(j, j'), ?_⟩
  rw [mem_ball, dist_eq_norm] at hj hj'
  rw [mem_ball, dist_eq_norm]
  have h : x - y - (c j - c j') = (x - c j) - (y - c j') := by abel
  change ‖x - y - (c j - c j')‖ < r j + r j'
  rw [h]
  exact (norm_sub_le _ _).trans_lt (add_lt_add hj hj')

theorem diff_integrable (c : κ → Space) (r : κ → ℝ) (k : ℝ) (i j : Fin 3) :
    IntegrableOn (fun z : Space => DyadicKernel.remainder k z i j) (diffSet c r) := by
  unfold diffSet
  rw [integrableOn_finite_iUnion]
  intro m
  exact (RealKernelBounds.remainder_integrable_ball k (‖c m.1 - c m.2‖ + (r m.1 + r m.2)) i j).mono_set
    (ball_subset_closedBall_norm _ _)

/-- The L1 mass of the dyadic remainder on the difference set is at most the sum of the ball masses. -/
theorem diff_mass (c : κ → Space) (r : κ → ℝ) (k : ℝ) (i j : Fin 3) :
    ∫ z in diffSet c r, ‖DyadicKernel.remainder k z i j‖ ≤
      ∑ m : κ × κ, (35/3 : ℝ) * k^2 * (r m.1 + r m.2)^2 := by
  have hf : ∀ m : κ × κ, IntegrableOn (fun z : Space => ‖DyadicKernel.remainder k z i j‖)
      (ball (c m.1 - c m.2) (r m.1 + r m.2)) := fun m =>
    ((RealKernelBounds.remainder_integrable_ball k (‖c m.1 - c m.2‖ + (r m.1 + r m.2)) i j).mono_set
      (ball_subset_closedBall_norm _ _)).norm
  have hindm : ∀ m : κ × κ, Integrable ((ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
      (fun z : Space => ‖DyadicKernel.remainder k z i j‖)) := fun m =>
    (hf m).integrable_indicator measurableSet_ball
  have hind : Integrable ((diffSet c r).indicator (fun z : Space => ‖DyadicKernel.remainder k z i j‖)) :=
    IntegrableOn.integrable_indicator (diff_integrable c r k i j).norm (diffSet_measurable c r)
  have hpt : ∀ z : Space, (diffSet c r).indicator (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z ≤
      ∑ m : κ × κ, (ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
        (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z := by
    intro z
    by_cases hz : z ∈ diffSet c r
    · rw [Set.indicator_of_mem hz]
      obtain ⟨m, hm⟩ := mem_iUnion.mp hz
      calc ‖DyadicKernel.remainder k z i j‖
          = (ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
              (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z := (Set.indicator_of_mem hm (fun z : Space => ‖DyadicKernel.remainder k z i j‖)).symm
        _ ≤ _ := Finset.single_le_sum (f := fun m : κ × κ => (ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
              (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z)
              (fun m _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) z) (Finset.mem_univ m)
    · rw [Set.indicator_of_not_mem hz]
      exact Finset.sum_nonneg (fun m _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) z)
  calc ∫ z in diffSet c r, ‖DyadicKernel.remainder k z i j‖
      = ∫ z, (diffSet c r).indicator (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z :=
        (integral_indicator (diffSet_measurable c r)).symm
    _ ≤ ∫ z, ∑ m : κ × κ, (ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
          (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z :=
        integral_mono hind (integrable_finset_sum _ (fun m _ => hindm m)) hpt
    _ = ∑ m : κ × κ, ∫ z, (ball (c m.1 - c m.2) (r m.1 + r m.2)).indicator
          (fun z : Space => ‖DyadicKernel.remainder k z i j‖) z :=
        integral_finset_sum _ (fun m _ => hindm m)
    _ = ∑ m : κ × κ, ∫ z in ball (c m.1 - c m.2) (r m.1 + r m.2), ‖DyadicKernel.remainder k z i j‖ :=
        Finset.sum_congr rfl (fun m _ => integral_indicator measurableSet_ball)
    _ ≤ _ := Finset.sum_le_sum (fun m _ => remainder_ball_mass k _ _ i j)

end Family

section Partner
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit quadratic bound of the remainder mass on the doubled difference set (balls of radius `ρ a`). -/
def massBound (N : ℕ) (ρ a : ℝ) : ℝ := (N : ℝ)^2 * ((140/3 : ℝ) * ρ^2 * a^2)

theorem massBound_nonneg (N : ℕ) (ρ a : ℝ) : 0 ≤ massBound N ρ a := by
  unfold massBound
  positivity

theorem partner_radius_const (ρ a : ℝ) (j : ι ⊕ ι) :
    RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a) j = ρ*a := by
  rcases j <;> rfl

theorem partner_mass_le (p : ℝ → ι → Space) (ρ a : ℝ) (i j : Fin 3) :
    ∫ z in diffSet (RestrictedTEPartnerBalls.partnerCentre (p a))
        (RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a)), ‖DyadicKernel.remainder 1 z i j‖ ≤
      massBound (Fintype.card (ι ⊕ ι)) ρ a := by
  refine (diff_mass _ _ 1 i j).trans_eq ?_
  simp only [partner_radius_const, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
  unfold massBound
  push_cast
  ring

/-- The quadratic bound of the dynamic remainder sandwich of the doubled device. -/
theorem partner_remainder_norm_le (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖DynamicVolume.weightedRemainder (RestrictedTEPartnerBalls.partnerCoefficient (p a) (fun _ : ι => ρ*a) χ hχ)
        1 b‖ ≤ 9*χ*massBound (Fintype.card (ι ⊕ ι)) ρ a := by
  have hin : ∀ l, ‖p a l‖+ρ*a ≤ R :=
    fun l => (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 l)
  have hc : ∀ x : Space, x ∉ closedBall (0 : Space) b →
      (RestrictedTEPartnerBalls.partnerCoefficient (p a) (fun _ : ι => ρ*a) χ hχ).value
        (VectorFourier.coordinateMap x) = 0 := fun x hx =>
    RestrictedTEPartnerBalls.partner_zero_outside (p a) (fun _ : ι => ρ*a) χ hχ R hin x
      (fun h => hx (closedBall_subset_closedBall hRb h))
  have h := WeightedRemainderSchur.weightedRemainder_norm_le_of_mass
    (RestrictedTEPartnerBalls.partnerCoefficient (p a) (fun _ : ι => ρ*a) χ hχ)
    (RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi a ha ha1) 1 b hc
    (diffSet (RestrictedTEPartnerBalls.partnerCentre (p a))
      (RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a)))
    (diffSet_measurable _ _)
    (fun x hx y hy => diff_mem _ _ x y hx hy)
    (fun i j => diff_integrable _ _ 1 i j)
    (massBound (Fintype.card (ι ⊕ ι)) ρ a) (fun i j => partner_mass_le p ρ a i j)
  exact h

/-- The carrier volume of the doubled device is cubic in the scale. -/
theorem partner_carrier_volume_le (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    volume.real (RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi a ha ha1).carrier ≤
      ((Fintype.card (ι ⊕ ι) : ℝ)*ρ^3*(Real.pi*4/3))*a^3 := by
  show volume.real (⋃ j, ball (RestrictedTEPartnerBalls.partnerCentre (p a) j)
    (RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a) j)) ≤ _
  refine (DynamicSupportVolume.finite_ball_volume _ _ (fun j => by
    rw [partner_radius_const]
    exact mul_nonneg hρ.le ha.le)).trans_eq ?_
  simp only [partner_radius_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The scale `a_n = (q^n)⁻¹`. -/
def scale (q : ℝ) (n : ℕ) : ℝ := (q^n)⁻¹

theorem scale_pos {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < scale q n := by
  unfold scale
  have : 0 < q := lt_trans zero_lt_one hq
  positivity

theorem scale_le_one {q : ℝ} (hq : 1 ≤ q) (n : ℕ) : scale q n ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ hq)

theorem scale_tendsto {q : ℝ} (hq : 1 < q) : Tendsto (fun n : ℕ => scale q n) atTop (𝓝 0) := by
  unfold scale
  exact (tendsto_pow_atTop_atTop_of_one_lt hq).inv_tendsto_atTop

theorem scale_gain {q : ℝ} (n : ℕ) : (1 : ℝ)/scale q n = q^n := by
  unfold scale
  rw [one_div, inv_inv]

theorem scale_identity {q : ℝ} (hq : 1 < q) (n : ℕ) : q^(2*n) * (scale q n)^2 = 1 := by
  have h0 : 0 < q := lt_trans zero_lt_one hq
  have hqn : 0 < q^n := pow_pos h0 n
  have h2 : q^(2*n) = (q^n)^2 := by rw [mul_comm, pow_mul]
  unfold scale
  rw [h2, inv_pow]
  field_simp

/-- The coefficient of the doubled device at scale `a_n = (q^n)⁻¹`. -/
abbrev deviceCoeff (p : ℝ → ι → Space) (ρ χ : ℝ) (hχ : 0 ≤ χ) (q : ℝ) (n : ℕ) : Coefficient :=
  RestrictedTEPartnerBalls.partnerCoefficient (p (scale q n)) (fun _ : ι => ρ*scale q n) χ hχ

/-- The support data of the doubled device at scale `a_n = (q^n)⁻¹`. -/
abbrev deviceData (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) (n : ℕ) :
    BoundedMaterialKernel.SupportData (deviceCoeff p ρ χ hχ q n) :=
  RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi (scale q n) (scale_pos hq n) (scale_le_one hq.le n)

theorem kernelConstant_le (q : ℝ) (hq : 1 ≤ q) (n : ℕ) :
    SourcePairedSmallInclusion.kernelConstant q n ≤
      9*(q^(2*n)+1)*SphereReactionKernel.entryBound 1 := by
  unfold SourcePairedSmallInclusion.kernelConstant
  have hx : 1 ≤ q^(2*n) := one_le_pow₀ hq
  have h1 : |q^(2*n)-1| ≤ q^(2*n) := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h2 : |(q^(2*n))⁻¹-1| ≤ 1 := by
    have h0 : 0 < (q^(2*n))⁻¹ := by positivity
    have h3 : (q^(2*n))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    rw [abs_le]
    constructor <;> linarith
  have hE := SphereReactionKernel.entryBound_nonnegative 1
  have h4 := add_le_add h1 h2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) hE

theorem kernelConstant_nonneg (q : ℝ) (n : ℕ) : 0 ≤ SourcePairedSmallInclusion.kernelConstant q n := by
  unfold SourcePairedSmallInclusion.kernelConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (SphereReactionKernel.entryBound_nonnegative 1)

/-- The explicit linear-in-scale constant of the data smallness. -/
def dataConstant (N : ℕ) (ρ χ : ℝ) : ℝ :=
  9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)) + 18*χ*((N : ℝ)*ρ^3*(Real.pi*4/3))*SphereReactionKernel.entryBound 1

theorem dataConstant_nonneg (N : ℕ) (ρ χ : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) : 0 ≤ dataConstant N ρ χ := by
  unfold dataConstant
  have hE := SphereReactionKernel.entryBound_nonnegative 1
  have h1 : 0 ≤ 9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)) := by positivity
  have h2 : 0 ≤ 18*χ*((N : ℝ)*ρ^3*(Real.pi*4/3)) := by positivity
  exact add_nonneg h1 (mul_nonneg h2 hE)

/-- The remainder sandwich norm and the limiting-inclusion term of the doubled device at scale `a_n` are at most
`dataConstant * a_n`. -/
theorem partner_data_bound (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) (n : ℕ) :
    ‖DynamicVolume.weightedRemainder (deviceCoeff p ρ χ hχ q n) 1 b‖ +
      (deviceCoeff p ρ χ hχ q n).bound * volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier *
        SourcePairedSmallInclusion.kernelConstant q n ≤
      dataConstant (Fintype.card (ι ⊕ ι)) ρ χ * scale q n := by
  have ha0 := scale_pos hq n
  have ha1 := scale_le_one hq.le n
  have hxa := scale_identity hq n
  have hE := SphereReactionKernel.entryBound_nonnegative 1
  set a := scale q n with ha
  set x : ℝ := q^(2*n) with hx
  set N : ℕ := Fintype.card (ι ⊕ ι) with hN
  set V : ℝ := (N : ℝ)*ρ^3*(Real.pi*4/3) with hV
  have hV0 : 0 ≤ V := by positivity
  have ha2 : a^2 ≤ a := by
    calc a^2 = a*a := by ring
      _ ≤ a*1 := mul_le_mul_of_nonneg_left ha1 ha0.le
      _ = a := mul_one a
  have ha3 : a^3 ≤ a := by
    calc a^3 = a*a^2 := by ring
      _ ≤ a*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha0.le ha1) ha0.le
      _ = a := mul_one a
  -- remainder term
  have hT1 : ‖DynamicVolume.weightedRemainder (deviceCoeff p ρ χ hχ q n) 1 b‖ ≤
      (9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)))*a := by
    refine (partner_remainder_norm_le p ρ χ R b hρ hχ hRb hi a ha0 ha1).trans ?_
    unfold massBound
    have hK : 0 ≤ 9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)) := by positivity
    calc 9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2*a^2)) = (9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)))*a^2 := by ring
      _ ≤ (9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)))*a := mul_le_mul_of_nonneg_left ha2 hK
  -- inclusion term
  have hvol := partner_carrier_volume_le p ρ χ R hρ hχ hi a ha0 ha1
  have hvol0 : 0 ≤ volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier := measureReal_nonneg
  have hkc := kernelConstant_le q hq.le n
  have hkc0 := kernelConstant_nonneg q n
  have hT2 : (deviceCoeff p ρ χ hχ q n).bound * volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier *
      SourcePairedSmallInclusion.kernelConstant q n ≤ (18*χ*V*SphereReactionKernel.entryBound 1)*a := by
    have hb : (deviceCoeff p ρ χ hχ q n).bound = χ := rfl
    rw [hb]
    have hs1 : χ * volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier ≤ χ*(V*a^3) :=
      mul_le_mul_of_nonneg_left hvol hχ
    have hs2 : χ * volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier *
        SourcePairedSmallInclusion.kernelConstant q n ≤ χ*(V*a^3)*(9*(x+1)*SphereReactionKernel.entryBound 1) :=
      mul_le_mul hs1 hkc hkc0 (by positivity)
    have hs3 : χ*(V*a^3)*(9*(x+1)*SphereReactionKernel.entryBound 1) =
        9*χ*V*SphereReactionKernel.entryBound 1*(a + a^3) := by
      linear_combination (9*χ*V*SphereReactionKernel.entryBound 1*a) * hxa
    have hK2 : 0 ≤ 9*χ*V*SphereReactionKernel.entryBound 1 := by positivity
    calc _ ≤ χ*(V*a^3)*(9*(x+1)*SphereReactionKernel.entryBound 1) := hs2
      _ = 9*χ*V*SphereReactionKernel.entryBound 1*(a + a^3) := hs3
      _ ≤ 9*χ*V*SphereReactionKernel.entryBound 1*(2*a) :=
          mul_le_mul_of_nonneg_left (by linarith) hK2
      _ = (18*χ*V*SphereReactionKernel.entryBound 1)*a := by ring
  calc _ ≤ (9*χ*((N : ℝ)^2*((140/3 : ℝ)*ρ^2)))*a + (18*χ*V*SphereReactionKernel.entryBound 1)*a :=
        add_le_add hT1 hT2
    _ = dataConstant N ρ χ * a := by
        unfold dataConstant
        ring

/-- Eventual smallness of the data of the doubled device at the scales `a_n = (q^n)⁻¹`. -/
theorem partner_dataSmallness (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop,
      ‖DynamicVolume.weightedRemainder (deviceCoeff p ρ χ hχ q n) 1 b‖ +
        (deviceCoeff p ρ χ hχ q n).bound * volume.real (deviceData p ρ χ R hρ hχ hi q hq n).carrier *
          SourcePairedSmallInclusion.kernelConstant q n < 1 := by
  have ht : Tendsto (fun n : ℕ => dataConstant (Fintype.card (ι ⊕ ι)) ρ χ * scale q n) atTop (𝓝 0) := by
    simpa using (scale_tendsto hq).const_mul (dataConstant (Fintype.card (ι ⊕ ι)) ρ χ)
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
  exact (partner_data_bound p ρ χ R b hρ hχ hRb hi q hq n).trans_lt hn

/-- The remainder sandwich norm of the doubled device tends to zero along the scales `a_n`. -/
theorem partner_remainder_tendsto (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => ‖DynamicVolume.weightedRemainder (deviceCoeff p ρ χ hχ q n) 1 b‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (9*χ*((Fintype.card (ι ⊕ ι) : ℝ)^2*((140/3 : ℝ)*ρ^2)))*(scale q n)^2)
      atTop (𝓝 0) := by
    simpa using ((scale_tendsto hq).pow 2).const_mul (9*χ*((Fintype.card (ι ⊕ ι) : ℝ)^2*((140/3 : ℝ)*ρ^2)))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  refine (partner_remainder_norm_le p ρ χ R b hρ hχ hRb hi (scale q n) (scale_pos hq n)
    (scale_le_one hq.le n)).trans_eq ?_
  unfold massBound
  ring

/-- Unit-ness of the limiting effective inclusion block of the doubled device for every fixed `q > 1`,
all large `n` and every enclosing radius `b ≥ R`. -/
theorem partner_limitEffective_isUnit (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hb : 0 < b) (hRb : R ≤ b) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop,
      IsUnit (SourcePairedReduction.limitEffective q hq.le n (deviceCoeff p ρ χ hχ q n)
        (deviceData p ρ χ R hρ hχ hi q hq n) b hb) := by
  filter_upwards [partner_dataSmallness p ρ χ R b hρ hχ hRb hi q hq] with n hn
  refine SourcePairedNormSmallness.limitEffective_isUnit_of_remainder_norm q hq.le n _ _ b hb
    (lt_of_le_of_lt ?_ hn)
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (SourcePairedSmallInclusion.limitKernelNorm_le q hq.le n b hb)
    (mul_nonneg (StaticCoefficient.bound_nonnegative _) measureReal_nonneg))

end Partner
end OQ14.RestrictedTEPartnerSmallness
#print axioms OQ14.RestrictedTEPartnerSmallness.volume_real_ball
#print axioms OQ14.RestrictedTEPartnerSmallness.ball_subset_closedBall_norm
#print axioms OQ14.RestrictedTEPartnerSmallness.inv_norm_ball_integral_le
#print axioms OQ14.RestrictedTEPartnerSmallness.remainder_ball_mass
#print axioms OQ14.RestrictedTEPartnerSmallness.diffSet_measurable
#print axioms OQ14.RestrictedTEPartnerSmallness.diff_mem
#print axioms OQ14.RestrictedTEPartnerSmallness.diff_integrable
#print axioms OQ14.RestrictedTEPartnerSmallness.diff_mass
#print axioms OQ14.RestrictedTEPartnerSmallness.massBound_nonneg
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_radius_const
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_mass_le
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_remainder_norm_le
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_carrier_volume_le
#print axioms OQ14.RestrictedTEPartnerSmallness.scale_pos
#print axioms OQ14.RestrictedTEPartnerSmallness.scale_le_one
#print axioms OQ14.RestrictedTEPartnerSmallness.scale_tendsto
#print axioms OQ14.RestrictedTEPartnerSmallness.scale_gain
#print axioms OQ14.RestrictedTEPartnerSmallness.scale_identity
#print axioms OQ14.RestrictedTEPartnerSmallness.kernelConstant_le
#print axioms OQ14.RestrictedTEPartnerSmallness.kernelConstant_nonneg
#print axioms OQ14.RestrictedTEPartnerSmallness.dataConstant_nonneg
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_data_bound
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_dataSmallness
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_remainder_tendsto
#print axioms OQ14.RestrictedTEPartnerSmallness.partner_limitEffective_isUnit
