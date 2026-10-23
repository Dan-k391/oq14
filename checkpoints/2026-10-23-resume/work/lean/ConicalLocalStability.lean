import ConicalLocalCoefficient
import ConicalLocalBounds
import ConicalProjectionLinear
import ConicalParticularLinear

/-! Quantitative stability of the actual local conical particular solution and extraction numerator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalLocalStability
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
  OQ14.ConicalLocalCoefficient OQ14.ConicalAnnularCoefficient OQ14.ConicalRadialParticular OQ14.WeakGreen
open scoped Topology
abbrev Space := Maxwell.Space

theorem particular_sub {p : Data} {a : ℝ} (s t : System p a) (hν : p.exponent < 1) (r : ℝ) (hr : 0 ≤ r) :
    particular p.exponent (radialCorrection (ConicalProjectionLinear.sub s t))
      (tangentCorrection (ConicalProjectionLinear.sub s t)) r=
      particular p.exponent (radialCorrection s) (tangentCorrection s) r-
        particular p.exponent (radialCorrection t) (tangentCorrection t) r := by
  rw [ConicalProjectionLinear.radialCorrection_sub,ConicalProjectionLinear.tangentCorrection_sub]
  exact ConicalParticularLinear.particular_sub p.exponent ⟨p.exponent_pos,hν⟩ _ _ _ _
    (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn
    (radialCorrection_continuous t).continuousOn (tangentCorrection_continuous t).continuousOn r hr

theorem particular_difference_bound (p : Data) (hν : p.exponent < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s t : System p a) (R M : ℝ), 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-t.correction i x‖ ≤ M) →
      ∀ r ∈ Ioc (0 : ℝ) R,
      ‖particular p.exponent (radialCorrection s) (tangentCorrection s) r-
        particular p.exponent (radialCorrection t) (tangentCorrection t) r‖ ≤ C*M*r := by
  obtain ⟨C,hC,hb⟩ := ConicalLocalBounds.particular_bound p hν
  refine ⟨C,hC,?_⟩
  intro a s t R M hM hW r hr
  rw [← particular_sub s t hν r hr.1.le]
  exact hb (ConicalProjectionLinear.sub s t) R M hM hW r hr

theorem correctionL2_sub {p : Data} {a : ℝ} (s t : System p a) (i : Fin 3) :
    correctionL2 (ConicalProjectionLinear.sub s t) i=correctionL2 s i-correctionL2 t i := by
  apply Lp.ext
  filter_upwards [correctionL2_ae (ConicalProjectionLinear.sub s t) i,
    correctionL2_ae s i,correctionL2_ae t i,Lp.coeFn_sub (correctionL2 s i) (correctionL2 t i)] with x hd hs ht hsub
  rw [hd,hsub]
  simp only [Pi.sub_apply,hs,ht,ConicalProjectionLinear.sub]

def correctionPair {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 s i)

def totalPair {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (totalCoordinate s i)

theorem gradientPair_eq {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    gradientPair s ζ hζ hc=totalPair s ζ hζ hc-correctionPair s ζ hζ hc := by
  simp only [ConicalLocalCoefficient.gradientPair,totalPair,correctionPair,totalCoordinate,map_add,Finset.sum_add_distrib]
  ring

theorem correctionPair_sub {p : Data} {a : ℝ} (s t : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    correctionPair (ConicalProjectionLinear.sub s t) ζ hζ hc=
      correctionPair s ζ hζ hc-correctionPair t ζ hζ hc := by
  simp only [correctionPair,correctionL2_sub,map_sub,Finset.sum_sub_distrib]

theorem correctionPair_difference_bound {p : Data} {a : ℝ} (s t : System p a) (R M : ℝ) (_hM : 0 ≤ M)
    (hW : ∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-t.correction i x‖ ≤ M)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ‖correctionPair s ζ hζ hc-correctionPair t ζ hζ hc‖ ≤ M*testMass p ζ := by
  rw [← correctionPair_sub]
  have hi (i : Fin 3) : ‖scalarProduct (testCoordinate p ζ hζ hc i)
      (correctionL2 (ConicalProjectionLinear.sub s t) i)‖ ≤
      M*(∫ x : Space, ‖(ConicalTangentialDivergence.tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) := by
    rw [scalarProduct_integral]
    have he : (∫ x : Space, testCoordinate p ζ hζ hc i x*correctionL2 (ConicalProjectionLinear.sub s t) i x)=
        ∫ x : Space, (ConicalTangentialDivergence.tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)*
          (s.correction i x-t.correction i x) := by
      apply integral_congr_ae
      filter_upwards [ConicalTangentialDivergence.tangentFieldL2_ae _ _ _ p.eigenvalue_bounds
        p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
        correctionL2_ae (ConicalProjectionLinear.sub s t) i] with x ht hw
      change testCoordinate p ζ hζ hc i x*correctionL2 (ConicalProjectionLinear.sub s t) i x=_
      rw [show testCoordinate p ζ hζ hc i x=(ConicalTangentialDivergence.tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ) from ht,hw]
      rfl
    rw [he,← integral_const_mul]
    apply norm_integral_le_of_norm_le ((test_integrable p ζ hζ hc i).norm.const_mul M)
    filter_upwards with x
    by_cases hz : ζ ‖x‖=0
    · simp only [ConicalTangentialDivergence.tangentField,hz,zero_mul,Complex.ofReal_zero,mul_zero,norm_zero]
      exact le_rfl
    · have hx : x ∈ closedBall (0 : Space) R := by
        simpa only [mem_closedBall,dist_zero_right] using (hs (subset_tsupport ζ hz)).2.le
      rw [norm_mul,mul_comm M]
      exact mul_le_mul_of_nonneg_left (hW i x hx) (norm_nonneg _)
  calc
    _ ≤ ∑ i : Fin 3, ‖scalarProduct (testCoordinate p ζ hζ hc i)
        (correctionL2 (ConicalProjectionLinear.sub s t) i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, M*(∫ x : Space,
        ‖(ConicalTangentialDivergence.tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [testMass,Finset.mul_sum]

end OQ14.ConicalLocalStability

#print axioms OQ14.ConicalLocalStability.particular_sub
#print axioms OQ14.ConicalLocalStability.particular_difference_bound
#print axioms OQ14.ConicalLocalStability.correctionL2_sub
#print axioms OQ14.ConicalLocalStability.gradientPair_eq
#print axioms OQ14.ConicalLocalStability.correctionPair_sub
#print axioms OQ14.ConicalLocalStability.correctionPair_difference_bound
