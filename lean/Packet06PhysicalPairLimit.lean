import Packet06SpatialAngularLimit
import Packet06AngularPairLimit
import ConicalLocalPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PhysicalPairLimit
open MeasureTheory Filter Set OQ14.Maxwell OQ14.WeakGreen OQ14.ConicalProjectionData
  OQ14.ConicalAnnularCoefficient OQ14.ConicalLocalStability OQ14.Packet06SpatialAngularLimit
open scoped Topology

theorem normalized_test_pair (p : ConicalStaticVolume.Data) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (i : Fin 3) (v : WeakCurl.L2Scalar) :
    scalarProduct ((angularTest_memLp ζ hζ.continuous hc p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i).toLp
        (angularTest ζ p.eigenvalue p.contrast p.threshold i)) v =
      ((p.threshold⁻¹ : ℝ) : ℂ)*scalarProduct (testCoordinate p ζ hζ hc i) v := by
  rw [scalarProduct_integral,scalarProduct_integral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(angularTest_memLp ζ hζ.continuous hc p.eigenvalue p.contrast p.threshold
    p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i).coeFn_toLp,
    ConicalTangentialDivergence.tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative
      p.threshold_pos p.threshold_lt_one ζ hζ hc i] with x hx hy
  change _ = ((p.threshold⁻¹ : ℝ) : ℂ)*(testCoordinate p ζ hζ hc i x*v x)
  rw [hx]
  change testCoordinate p ζ hζ hc i x = _ at hy
  rw [hy,ConicalGraphMoments.tangent_field_identity]
  simp only [angularTest]
  ring

theorem actual_total_pair_tendsto (p : ℕ → ConicalStaticVolume.Data) (ell d : ℕ → ℝ)
    (hellp : ∀ j, (p j).eigenvalue = ell j) (hdp : ∀ j, (p j).contrast = d j)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (htp : ∀ j, (p j).threshold = t)
    (hell : Tendsto ell atTop (𝓝 2)) (hd : Tendsto d atTop (𝓝 0))
    (hellb : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (D : ℝ) (hD : 0 ≤ D) (hdb : ∀ j, d j ∈ Icc (0 : ℝ) D)
    (b : ℝ) (s : ∀ j, System (p j) b) (g : ℕ → ConicalRungeBall.BallL2 b)
    (g₀ : ConicalRungeBall.BallL2 b) (hg : Tendsto g atTop (𝓝 g₀))
    (hactual : ∀ j i, (g j i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (Metric.closedBall 0 b)] totalCoordinate (s j) i)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b) :
    Tendsto (fun j => totalPair (s j) ζ hζ hc) atTop
      (𝓝 ((t : ℂ)*∑ i : Fin 3, scalarProduct ((limitTest_memLp ζ hζ.continuous hc t ht ht1 i).toLp (limitTest ζ i))
        (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g₀) i))) := by
  have hpair (i : Fin 3) := Packet06SpatialAngularLimit.angularTest_tendsto ell d hell hd hellb D hD hdb t ht ht1 ζ hζ.continuous hc i
  have hv (i : Fin 3) : Tendsto (fun j => NewtonL2.physicalCoordinate (ConicalBallExtension.vector b (g j)) i) atTop
      (𝓝 (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g₀) i)) := by
    change Tendsto (fun j => DynamicConvolution.component i (ConicalBallExtension.vector b (g j))) atTop _
    exact ((DynamicConvolution.component i).continuous.tendsto _).comp
      (((ConicalBallExtension.vector b).continuous.tendsto _).comp hg)
  have hsum := tendsto_finset_sum Finset.univ (fun i _ =>
    Packet06AngularPairLimit.scalar_pair_tendsto _ _ _ _ (hpair i) (hv i))
  have he (j : ℕ) :
      (∑ i : Fin 3, scalarProduct ((angularTest_memLp ζ hζ.continuous hc (ell j) (d j) t
        (hellb j) (hdb j).1 ht ht1 i).toLp (angularTest ζ (ell j) (d j) t i))
        (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b (g j)) i)) =
      ((t⁻¹ : ℝ) : ℂ)*totalPair (s j) ζ hζ hc := by
    rw [ConicalLocalPairing.totalPair_eq (s j) (g j) ζ hζ hc hs (hactual j)]
    simp only [ConicalLocalPairing.ballPair,ContinuousLinearMap.comp_apply,fieldPair_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := normalized_test_pair (p j) ζ hζ hc i (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b (g j)) i)
    simpa only [hellp j,hdp j,htp j] using h
  simp_rw [he] at hsum
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h := hsum.const_mul (t : ℂ)
  simpa only [Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ ht0,one_mul] using h

#print axioms OQ14.Packet06PhysicalPairLimit.normalized_test_pair
#print axioms OQ14.Packet06PhysicalPairLimit.actual_total_pair_tendsto
end OQ14.Packet06PhysicalPairLimit
