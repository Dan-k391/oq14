import ConicalCoefficientStability
import ConicalBallExtension

/-! The actual conical annular extraction pairing is bounded by physical ball L2 data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalLocalPairing
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalProjectionData OQ14.ConicalAnnularCoefficient OQ14.ConicalLocalStability
  OQ14.ConicalTangentialDivergence OQ14.PolarMomentTesting OQ14.WeakGreen
open scoped Topology
abbrev Space := Maxwell.Space

def ballPair (p : Data) (a : ℝ) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    ConicalRungeBall.BallL2 a →L[ℂ] ℂ :=
  (fieldPair p ζ hζ hc).comp (ConicalBallExtension.vector a)

theorem totalPair_eq {p : Data} {a b : ℝ} (s : System p a)
    (g : ConicalRungeBall.BallL2 b) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b)
    (hg : ∀ i, (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) b)] totalCoordinate s i) :
    totalPair s ζ hζ hc=ballPair p b ζ hζ hc g := by
  rw [ballPair,ContinuousLinearMap.comp_apply,fieldPair_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarProduct_integral,scalarProduct_integral]
  have hl := (ae_restrict_iff' measurableSet_closedBall).mp (hg i)
  apply integral_congr_ae
  filter_upwards [ConicalBallExtension.vector_ae b g i,hl,
    tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i]
    with x he hg ht
  change testCoordinate p ζ hζ hc i x*totalCoordinate s i x=
    testCoordinate p ζ hζ hc i x*NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g) i x
  rw [he]
  by_cases hx : x ∈ closedBall (0 : Space) b
  · rw [indicator_of_mem hx,hg hx]
  · have hz : ζ ‖x‖=0 := image_eq_zero_of_nmem_tsupport (fun h => hx (by
      simpa only [mem_closedBall,dist_zero_right] using (hs h).2.le))
    change tangentFieldL2 _ _ _ _ _ _ _ ζ hζ hc i x=_ at ht
    change testCoordinate p ζ hζ hc i x=_ at ht
    rw [ht]
    simp only [tangentField,hz,Complex.ofReal_zero,zero_mul,mul_zero]

theorem totalPair_difference_bound {p : Data} {a b : ℝ} (s t : System p a)
    (g h : ConicalRungeBall.BallL2 b) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b)
    (hg : ∀ i, (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) b)] totalCoordinate s i)
    (hh : ∀ i, (h i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) b)] totalCoordinate t i) :
    ‖totalPair s ζ hζ hc-totalPair t ζ hζ hc‖ ≤ ‖ballPair p b ζ hζ hc‖*‖g-h‖ := by
  rw [totalPair_eq s g ζ hζ hc hs hg,totalPair_eq t h ζ hζ hc hs hh,← map_sub]
  exact (ballPair p b ζ hζ hc).le_opNorm _

theorem numerator_difference_bound (p : Data) (hν : p.exponent < 1) (R b : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) (hRb : R ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s t : System p a), R ≤ a →
      ∀ (g h : ConicalRungeBall.BallL2 b),
      (∀ i, (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) b)] totalCoordinate s i) →
      (∀ i, (h i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) b)] totalCoordinate t i) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x-t.correction i x‖ ≤ M) →
      ‖ConicalCoefficientStability.numerator s ζ hζ hc-ConicalCoefficientStability.numerator t ζ hζ hc‖ ≤
        ‖ballPair p b ζ hζ hc‖*‖g-h‖+C*M := by
  obtain ⟨C,hC,hbound⟩ := ConicalCoefficientStability.numerator_difference_bound p hν R ζ hζ hc hs
  refine ⟨C,hC,?_⟩
  intro a s t hRa g h hg hh M hM hW
  exact (hbound s t hRa M hM hW).trans (add_le_add_right
    (totalPair_difference_bound s t g h ζ hζ hc (hs.trans (Ioo_subset_Ioo_right hRb)) hg hh) _)

end OQ14.ConicalLocalPairing
#print axioms OQ14.ConicalLocalPairing.totalPair_eq
#print axioms OQ14.ConicalLocalPairing.totalPair_difference_bound
#print axioms OQ14.ConicalLocalPairing.numerator_difference_bound

