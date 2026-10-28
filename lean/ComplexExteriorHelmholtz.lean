import CompactSmoothSchwartz
import ComplexExteriorWeak
import RegionalMaxwellHelmholtz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexExteriorHelmholtz
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ComplexResponseTests OQ14.ComplexExteriorWeak
  OQ14.WeakHelmholtzRegularity OQ14.ExteriorHelmholtz
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem actual_weak_helmholtz (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2)
    (i : Fin 3) : IsWeakHelmholtz z ((ball 0 T) \ (closedBall 0 1))
      (fun x => ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u (VectorFourier.coordinateMap x) i) := by
  intro φ hφ hc hs
  let s := CompactSmoothSchwartz.ofCompact φ hφ hc
  let f : Test := ⟨s, hc⟩
  have hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T := hs.trans (fun x hx => ball_subset_closedBall hx.1)
  have ho : tsupport (f.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ := hs.trans (fun x hx => hx.2)
  have h := component_helmholtz_test n hn z hz T hT u i f hf ho
  simp only [pair, testPair_integral] at h
  have hi (j : Fin 3) : Integrable (fun x : Space =>
      ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u (VectorFourier.coordinateMap x) i *
        (testPartial j (testPartial j f)).val x) := by
    have ht := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)
      (testPartial j (testPartial j f)).val
    apply ht.congr
    filter_upwards [NewtonL2.physicalCoordinate_ae
      (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i] with x hx
    rw [hx]
  have h0 : Integrable (fun x : Space =>
      ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u (VectorFourier.coordinateMap x) i * f.val x) := by
    have ht := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i) f.val
    apply ht.congr
    filter_upwards [NewtonL2.physicalCoordinate_ae
      (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i] with x hx
    rw [hx]
  have hd (j : Fin 3) : (GradientProjection.pderivative j s : Space → ℂ) =
      fun y => dcoord φ y j := by
    funext y
    rfl
  have he : (fun x : Space => ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
        (VectorFourier.coordinateMap x) i * (laplacian φ x + z^2*φ x)) =
      fun x => (∑ j : Fin 3, ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
        (VectorFourier.coordinateMap x) i * (testPartial j (testPartial j f)).val x) +
          z^2 * (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
            (VectorFourier.coordinateMap x) i * f.val x) := by
    funext x
    simp only [laplacian, testPartial, GradientProjection.pderivative_apply,
      CompactSmoothSchwartz.ofCompact_apply, f, hd, mul_add, Finset.mul_sum]
    simp only [show s x = φ x from rfl]
    ring
  rw [he, integral_add (integrable_finset_sum _ (fun j _ => hi j)) (h0.const_mul _),
    integral_finset_sum _ (fun j _ => hi j), integral_const_mul]
  exact h

theorem actual_locallyIntegrable (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (u : VectorL2)
    (i : Fin 3) : LocallyIntegrable (fun x => ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
      (VectorFourier.coordinateMap x) i) := by
  apply HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls
  intro Q
  apply ((Lp.memLp (NewtonL2.physicalCoordinate
    (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)).restrict _).ae_eq
  exact ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae _ i)

#print axioms OQ14.ComplexExteriorHelmholtz.actual_locallyIntegrable
#print axioms OQ14.ComplexExteriorHelmholtz.actual_weak_helmholtz
end OQ14.ComplexExteriorHelmholtz





