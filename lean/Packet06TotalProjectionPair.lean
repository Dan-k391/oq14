import Packet06AngularPairLimit
import ConicalLocalStability
import ConicalIntrinsicCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06TotalProjectionPair
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData
  OQ14.ConicalAnnularCoefficient OQ14.ConicalTangentialDivergence OQ14.ConicalGraphMoments
  OQ14.ConicalMomentWeights OQ14.PolarMomentTesting OQ14.ConicalLocalStability OQ14.WeakGreen

theorem total_pairing {p : ConicalStaticVolume.Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    totalPair s ζ hζ hc=(p.eigenvalue : ℂ)*
      ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalIntrinsicCoefficient.totalProjected s r := by
  have hi (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(ζ r : ℂ)*
      moment (totalCoordinate s i) (tangent p.eigenvalue p.contrast p.threshold i) r) (Ioi (0 : ℝ)) := by
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment _ (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _
      (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  have hp (i : Fin 3) : scalarProduct (testCoordinate p ζ hζ hc i) (totalCoordinate s i)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*moment (totalCoordinate s i) (tangent p.eigenvalue p.contrast p.threshold i) r := by
    rw [scalarProduct_integral]
    have he : (∫ x : Maxwell.Space, testCoordinate p ζ hζ hc i x*totalCoordinate s i x)=
        ∫ x : Maxwell.Space, totalCoordinate s i x*tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(ζ ‖x‖ : ℂ) := by
      apply integral_congr_ae
      filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i] with x hx
      change testCoordinate p ζ hζ hc i x*totalCoordinate s i x=_
      dsimp only [testCoordinate]
      rw [hx,ConicalGraphMoments.tangent_field_identity]
      ring
    rw [he]
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integral_weighted_moment _ (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _
      (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  rw [totalPair]
  simp only [hp]
  rw [← integral_finset_sum _ (fun i _ => hi i),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  simp only [← Finset.mul_sum,ConicalIntrinsicCoefficient.totalProjected,ConicalLocalFlux.tangentTotal]
  field_simp [Complex.ofReal_ne_zero.mpr (ConicalGraphProjection.eigenvalue_pos p).ne']
  ring
#print axioms OQ14.Packet06TotalProjectionPair.total_pairing
end OQ14.Packet06TotalProjectionPair
