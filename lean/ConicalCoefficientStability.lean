import ConicalLocalStability

/-! Actual annular extraction numerator is stable under total L2 pairings and local uniform correction changes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalCoefficientStability
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
  OQ14.ConicalLocalCoefficient OQ14.ConicalLocalStability OQ14.ConicalAnnularCoefficient
open scoped Topology
abbrev Space := Maxwell.Space

private theorem pair_integrable {p : Data} {a : ℝ} (s : System p a) (hν : p.exponent < 1)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) a) :
    IntegrableOn (fun r : ℝ => (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.particular p.exponent
      (radialCorrection s) (tangentCorrection s) r) (Ioi (0 : ℝ)) := by
  have hpLoc := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((ConicalFiniteExpansion.particular_memLp p.exponent a ⟨p.exponent_pos,hν⟩
      (radialCorrection s) (tangentCorrection s) (radialCorrection_continuous s).continuousOn
      (tangentCorrection_continuous s).continuousOn).locallyIntegrable (by norm_num))
  have hη : Continuous (fun r : ℝ => r*ζ r) := continuous_id.mul hζ.continuous
  have hcη : HasCompactSupport (fun r : ℝ => r*ζ r) := hc.mul_left
  have hi := SmoothLocalRepresentative.cutoff_integrable _ _ hpLoc (fun r => r*ζ r) hη hcη
    (tsupport_mul_subset_right.trans hs)
  simpa only [Complex.ofReal_mul] using hi.integrableOn

theorem particularPair_sub_integral {p : Data} {a : ℝ} (s t : System p a) (hν : p.exponent < 1)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) a) :
    particularPair s ζ-particularPair t ζ=(p.eigenvalue : ℂ)*
      ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*
        (ConicalRadialParticular.particular p.exponent (radialCorrection s) (tangentCorrection s) r-
          ConicalRadialParticular.particular p.exponent (radialCorrection t) (tangentCorrection t) r) := by
  rw [particularPair,particularPair,← mul_sub,← integral_sub
    (pair_integrable s hν ζ hζ hc hs) (pair_integrable t hν ζ hζ hc hs)]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  ring

theorem particularPair_difference_bound (p : Data) (hν : p.exponent < 1) (R : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s t : System p a), R ≤ a → ∀ M : ℝ, 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-t.correction i x‖ ≤ M) →
      ‖particularPair s ζ-particularPair t ζ‖ ≤ C*M := by
  obtain ⟨C,hC,hb⟩ := particular_difference_bound p hν
  have hi : IntegrableOn (fun r : ℝ => r^2*|ζ r|) (Ioi (0 : ℝ)) :=
    ((continuous_id.pow 2).mul hζ.continuous.abs).integrable_of_hasCompactSupport (μ := volume)
      (hc.norm.mul_left) |>.integrableOn
  let I : ℝ := ∫ r in Ioi (0 : ℝ), r^2*|ζ r|
  have hI : 0 ≤ I := integral_nonneg (fun r => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  refine ⟨‖(p.eigenvalue : ℂ)‖*C*I,mul_nonneg (mul_nonneg (norm_nonneg _) hC) hI,?_⟩
  intro a s t hRa M hM hW
  have hs' : tsupport ζ ⊆ Ioo (0 : ℝ) a := hs.trans (Ioo_subset_Ioo_right hRa)
  rw [particularPair_sub_integral s t hν ζ hζ hc hs',norm_mul]
  have hpair : ‖∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*
        (ConicalRadialParticular.particular p.exponent (radialCorrection s) (tangentCorrection s) r-
          ConicalRadialParticular.particular p.exponent (radialCorrection t) (tangentCorrection t) r)‖ ≤ C*M*I := by
    dsimp only [I]
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hi.const_mul (C*M))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hz : ζ r=0
    · simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero,abs_zero]
      exact le_rfl
    · have hri := (hs (subset_tsupport ζ hz)).2
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      have hh := mul_le_mul_of_nonneg_left (hb s t R M hM hW r ⟨hr,hri.le⟩)
        (mul_nonneg hr.le (abs_nonneg (ζ r)))
      convert hh using 1
      ring
  exact (mul_le_mul_of_nonneg_left hpair (norm_nonneg _)).trans_eq (by ring)

def numerator {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ConicalLocalCoefficient.gradientPair s ζ hζ hc-particularPair s ζ

theorem numerator_difference_bound (p : Data) (hν : p.exponent < 1) (R : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s t : System p a), R ≤ a → ∀ M : ℝ, 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-t.correction i x‖ ≤ M) →
      ‖numerator s ζ hζ hc-numerator t ζ hζ hc‖ ≤
        ‖totalPair s ζ hζ hc-totalPair t ζ hζ hc‖+C*M := by
  obtain ⟨C,hC,hb⟩ := particularPair_difference_bound p hν R ζ hζ hc hs
  have hMass : 0 ≤ testMass p ζ := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => norm_nonneg _))
  refine ⟨testMass p ζ+C,add_nonneg hMass hC,?_⟩
  intro a s t hRa M hM hW
  have hcorr := correctionPair_difference_bound s t R M hM hW ζ hζ hc hs
  have hpart := hb s t hRa M hM hW
  have he : numerator s ζ hζ hc-numerator t ζ hζ hc=
      ((totalPair s ζ hζ hc-totalPair t ζ hζ hc)-
        (correctionPair s ζ hζ hc-correctionPair t ζ hζ hc))-(particularPair s ζ-particularPair t ζ) := by
    rw [numerator,numerator,gradientPair_eq s,gradientPair_eq t]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add_right (norm_sub_le _ _) _).trans
  apply (add_le_add (add_le_add_left hcorr _) hpart).trans_eq
  ring

end OQ14.ConicalCoefficientStability

#print axioms OQ14.ConicalCoefficientStability.particularPair_sub_integral
#print axioms OQ14.ConicalCoefficientStability.particularPair_difference_bound
#print axioms OQ14.ConicalCoefficientStability.numerator_difference_bound
