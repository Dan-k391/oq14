import Packet05LocalGreenHessian

/-! The actual complex scalar Green potential has the expected first local
weak derivatives, with no regularity assumed of the source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalGreenGradient
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.PartialSmoothing
  OQ14.DynamicSource OQ14.KernelConvolution OQ14.Packet05LocalGreenRepresentatives
  OQ14.Packet05ComplexCorrectionRegularity
open scoped Topology SchwartzMap

def potentialRepresentative (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ))
    (hs : ∀ y, y ∉ closedBall 0 S → F y = 0) : NewtonL2.ScalarL2 :=
  ballRepresentative R _ (LocalConvolution.response_memLp_ball _
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) F hF F
    (Filter.EventuallyEq.rfl) R S hs)

theorem potential_local_gradient (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hc : HasCompactSupport (F : Space → ℂ))
    (hs : ∀ y, y ∉ closedBall 0 S → F y = 0) (j : Fin 3) :
    HasPartialOn (ball 0 R) (potentialRepresentative z R S F hF hs)
      (gradientRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) j) j := by
  intro φ hφ
  let ψ : DomainCurl.Test (ball 0 R) := ⟨φ, hφ⟩
  obtain ⟨K, f, hK, hKV, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation isOpen_ball ψ
  let U := potentialRepresentative z R S F hF hs
  let D := gradientRepresentative z R S F F hF hs (Filter.EventuallyEq.rfl) j
  have hu := ballRepresentative_ae R _ (LocalConvolution.response_memLp_ball _
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) F hF F
    (Filter.EventuallyEq.rfl) R S hs)
  have hv := ballRepresentative_ae R _ (gradient_response_memLp_ball z R S F F hF hs
    (Filter.EventuallyEq.rfl) j)
  have ht (n : ℕ) : HasCompactSupport (f n : Space → ℂ) :=
    hK.of_isClosed_subset isClosed_closure (hfK n)
  have he (n : ℕ) : scalarProduct D (FourierL2.embed (f n)) +
      scalarProduct U (FourierL2.embed (GradientProjection.pderivative j (f n))) = 0 := by
    let t : OQ14.DynamicSource.Test := ⟨f n, ht n⟩
    have hw := Packet06ComplexPotentialPair.gradient_pairing z F hF hc j t
    rw [← Packet06ComplexPotentialPair.potential_pairing z F hF hc (testPartial j t)] at hw
    have hvpair : scalarProduct D (FourierL2.embed (f n)) =
        ∫ x, response (fun y => ComplexGreenKernel.phiGradient z y j) F x * f n x := by
      rw [scalarProduct_embed]
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
    have hupair : scalarProduct U (FourierL2.embed (GradientProjection.pderivative j (f n))) =
        ∫ x, response (ComplexGreenKernel.phi z) F x * (testPartial j t).val x := by
      rw [scalarProduct_embed]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases h : x ∈ closedBall 0 R
      · rw [show U x = response (ComplexGreenKernel.phi z) F x from hx h]
        rfl
      · have hz : (GradientProjection.pderivative j (f n)) x = 0 := by
          rw [GradientProjection.pderivative_apply]
          have hn : x ∉ tsupport (f n : Space → ℂ) := by
            intro hx
            exact h (ball_subset_closedBall (hKV (hfK n hx)))
          simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
        simp [hz, testPartial, t]
    rw [hvpair, hupair]
    linear_combination hw
  have hlim := ((scalarProduct D).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct U).continuous.tendsto _ |>.comp (hd j))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun n => (he n).symm)))
  simpa only [ψ, U, D, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

end OQ14.Packet05LocalGreenGradient
#print axioms OQ14.Packet05LocalGreenGradient.potential_local_gradient
