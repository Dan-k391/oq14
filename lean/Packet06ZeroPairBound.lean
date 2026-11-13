import Packet06TotalProjectionPair
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ZeroPairBound
open Set Metric MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData
  OQ14.ConicalLocalStability

theorem estimate (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ C ≥ (0 : ℝ), ∀ (p : ConicalStaticVolume.Data) (_hpt : p.threshold = t)
      (_hpd : p.contrast ≤ D) (hν : p.exponent < 1) (_hhalf : (1/2 : ℝ) ≤ p.exponent)
      (b : ℝ) (hb : 0 < b) (hbi : b < p.cutoff.rIn) (M : ℝ) (s : System p b), 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Maxwell.Space) b → ‖s.correction i x-s.correction i 0‖ ≤ M*‖x‖^α) →
      ConicalIntrinsicCoefficient.coefficient s hb hbi hν = 0 →
      ∀ (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ),
      tsupport ζ ⊆ Ioo (0 : ℝ) b →
      ‖totalPair s ζ hζ hc‖ ≤ C*M*∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r| := by
  obtain ⟨C,hC,hbound⟩ := Packet06ConeZeroProjection.zero_coefficient_bound t D α ht ht1 hD hα
  refine ⟨2*C,by positivity,?_⟩
  intro p hpt hpd hν hhalf b hb hbi M s hM hW hz ζ hζ hc hs
  have hpr := hbound p hpt hpd hν hhalf b hb hbi M s hM hW hz
  have hI : IntegrableOn (fun r : ℝ => r^(2+α)*|ζ r|) (Ioi (0 : ℝ)) := by
    have hcont : Continuous (fun r : ℝ => r^(2+α)*|ζ r|) :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ 2+α)).mul hζ.continuous.abs
    exact (hcont.integrable_of_hasCompactSupport (hc.norm.mul_left)).integrableOn
  have hInt : ‖∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalIntrinsicCoefficient.totalProjected s r‖ ≤
      C*M*∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r| := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hI.const_mul (C*M))
    have hpr' := ae_restrict_of_ae (s := Ioi (0 : ℝ)) (ae_imp_of_ae_restrict hpr)
    filter_upwards [hpr',ae_restrict_mem measurableSet_Ioi] with r hp hr
    by_cases hmem : r ∈ Ioo (0 : ℝ) b
    · have hh := hp hmem
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      have hm : 0 ≤ r*|ζ r| := mul_nonneg hr.le (abs_nonneg _)
      have hpow : r*r^(1+α) = r^(2+α) := by
        calc
          r*r^(1+α) = r^(1 : ℝ)*r^(1+α) := by rw [Real.rpow_one]
          _ = r^(2+α) := by rw [← Real.rpow_add hr]; congr 1; ring
      calc
        _ ≤ (r*|ζ r|)*(C*M*r^(1+α)) := mul_le_mul_of_nonneg_left hh hm
        _ = _ := by rw [← hpow]; ring
    · have hz' : ζ r = 0 := image_eq_zero_of_nmem_tsupport (fun hh => hmem (hs hh))
      simp [hz']
  rw [Packet06TotalProjectionPair.total_pairing s ζ hζ hc,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg p.eigenvalue_bounds.1]
  have hInt0 : 0 ≤ ∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r| := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)
  calc
    _ ≤ p.eigenvalue*(C*M*∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) :=
      mul_le_mul_of_nonneg_left hInt p.eigenvalue_bounds.1
    _ ≤ 2*(C*M*∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) :=
      mul_le_mul_of_nonneg_right p.eigenvalue_bounds.2 (mul_nonneg (mul_nonneg hC hM) hInt0)
    _ = _ := by ring
#print axioms OQ14.Packet06ZeroPairBound.estimate
end OQ14.Packet06ZeroPairBound
