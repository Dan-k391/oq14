import Packet05LocalGreenRepresentatives

/-! The genuine Green-gradient response has the Newton-plus-dynamic weak
Hessian on every smaller open ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalGreenHessian
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.DynamicSource OQ14.KernelConvolution OQ14.Packet05LocalGreenRepresentatives
  OQ14.Packet05ComplexCorrectionRegularity OQ14.PartialSmoothing
open scoped Topology SchwartzMap

theorem gradient_local_hessian (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hc : HasCompactSupport (F : Space → ℂ))
    (hs : ∀ y, y ∉ closedBall 0 S → F y = 0) (i j : Fin 3) :
    HasPartialOn (ball 0 R)
      (gradientRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) j)
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
        (Packet05ScalarNewtonEmbedding.scalarSource F j)) i +
        dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i j) i := by
  intro φ hφ
  let ψ : DomainCurl.Test (ball 0 R) := ⟨φ, hφ⟩
  obtain ⟨K, f, hK, hKV, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation isOpen_ball ψ
  let U := gradientRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) j
  let D := NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
        (Packet05ScalarNewtonEmbedding.scalarSource F j)) i +
        dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i j
  have hu := ballRepresentative_ae R _ (gradient_response_memLp_ball z R S F F hF hs
    (Filter.EventuallyEq.rfl) j)
  have hv := ballRepresentative_ae R _ (dynamic_hessian_response_memLp_ball z R S F F hF hs
    (Filter.EventuallyEq.rfl) i j)
  have ht (n : ℕ) : HasCompactSupport (f n : Space → ℂ) :=
    hK.of_isClosed_subset isClosed_closure (hfK n)
  have he (n : ℕ) : scalarProduct D (FourierL2.embed (f n)) +
      scalarProduct U (FourierL2.embed (GradientProjection.pderivative i (f n))) = 0 := by
    let t : OQ14.DynamicSource.Test := ⟨f n, ht n⟩
    have hw := Packet05ComplexFullHessian.complex_hessian_weak_pairing z F hF hc i j t
    have hvpair : scalarProduct D (FourierL2.embed (f n)) =
        (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
          (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f n x) +
        (∫ x, response (fun y => Packet06ComplexHessian.hessianDifference z y i j) F x * f n x) := by
      rw [scalarProduct_embed]
      have ha := NewtonL2.scalar_pairing_integrable
        (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
          (Packet05ScalarNewtonEmbedding.scalarSource F j)) i) (f n)
      have hb := NewtonL2.scalar_pairing_integrable
        (dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i j) (f n)
      have heq : (∫ x, D x * f n x) =
          (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
            (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f n x) +
          (∫ x, dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i j x * f n x) := by
        rw [← integral_add ha hb]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
          (Packet05ScalarNewtonEmbedding.scalarSource F j)) i)
          (dynamicHessianRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) i j)] with x hx
        simp only [D, hx, Pi.add_apply, add_mul]
      rw [heq]
      congr 1
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      by_cases h : x ∈ closedBall 0 R
      · exact congrArg (fun v : ℂ => v * f n x) (hx h)
      · have hz : f n x = 0 := by
          have hn : x ∉ tsupport (f n : Space → ℂ) := by
            intro hx
            exact h (ball_subset_closedBall (hKV (hfK n hx)))
          exact (not_mem_tsupport_iff_eventuallyEq.mp hn).self_of_nhds
        simp [hz]
    have hupair : scalarProduct U (FourierL2.embed (GradientProjection.pderivative i (f n))) =
        ∫ x, response (fun y => ComplexGreenKernel.phiGradient z y j) F x * (testPartial i t).val x := by
      rw [scalarProduct_embed]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases h : x ∈ closedBall 0 R
      · rw [show U x = response (fun y => ComplexGreenKernel.phiGradient z y j) F x from hx h]
        rfl
      · have hz : (GradientProjection.pderivative i (f n)) x = 0 := by
          rw [GradientProjection.pderivative_apply]
          have hn : x ∉ tsupport (f n : Space → ℂ) := by
            intro hx
            exact h (ball_subset_closedBall (hKV (hfK n hx)))
          simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
        simp [hz, testPartial, t]
    rw [hvpair, hupair]
    linear_combination hw
  have hlim := ((scalarProduct D).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct U).continuous.tendsto _ |>.comp (hd i))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun n => (he n).symm)))
  simpa only [ψ, U, D, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

end OQ14.Packet05LocalGreenHessian
#print axioms OQ14.Packet05LocalGreenHessian.gradient_local_hessian
