import CompactSmoothSchwartz
import RegionalMaxwellHelmholtz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexSphereHelmholtz
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ComplexResponseTests OQ14.ComplexSphereWeak
  OQ14.WeakHelmholtzRegularity OQ14.ExteriorHelmholtz
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem actual_weak_helmholtz (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) : IsWeakHelmholtz (z*n) (ball 0 1)
      (fun x => response (ModalWeightedMode.coefficient n hn) z 1 u (VectorFourier.coordinateMap x) i) := by
  intro φ hφ hc hs
  let s := CompactSmoothSchwartz.ofCompact φ hφ hc
  let f : Test := ⟨s, hc⟩
  have hf : tsupport (f.val : Space → ℂ) ⊆ ball 0 1 := hs
  have h := component_helmholtz_test n hn z hz u hker i f hf
  simp only [pair, testPair_integral] at h
  have hi (j : Fin 3) : Integrable (fun x : Space =>
      response (ModalWeightedMode.coefficient n hn) z 1 u (VectorFourier.coordinateMap x) i *
        (testPartial j (testPartial j f)).val x) := by
    have ht := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) i)
      (testPartial j (testPartial j f)).val
    apply ht.congr
    filter_upwards [NewtonL2.physicalCoordinate_ae
      (response (ModalWeightedMode.coefficient n hn) z 1 u) i] with x hx
    rw [hx]
  have h0 : Integrable (fun x : Space =>
      response (ModalWeightedMode.coefficient n hn) z 1 u (VectorFourier.coordinateMap x) i * f.val x) := by
    have ht := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) i) f.val
    apply ht.congr
    filter_upwards [NewtonL2.physicalCoordinate_ae
      (response (ModalWeightedMode.coefficient n hn) z 1 u) i] with x hx
    rw [hx]
  have hd (j : Fin 3) : (GradientProjection.pderivative j s : Space → ℂ) =
      fun y => dcoord φ y j := by
    funext y
    rfl
  have he : (fun x : Space => response (ModalWeightedMode.coefficient n hn) z 1 u
        (VectorFourier.coordinateMap x) i * (laplacian φ x + (z*n)^2*φ x)) =
      fun x => (∑ j : Fin 3, response (ModalWeightedMode.coefficient n hn) z 1 u
        (VectorFourier.coordinateMap x) i * (testPartial j (testPartial j f)).val x) +
          (z*n)^2 * (response (ModalWeightedMode.coefficient n hn) z 1 u
            (VectorFourier.coordinateMap x) i * f.val x) := by
    funext x
    simp only [laplacian, testPartial, GradientProjection.pderivative_apply,
      CompactSmoothSchwartz.ofCompact_apply, f, hd, mul_add, Finset.mul_sum]
    simp only [show s x = φ x from rfl]
    ring
  rw [he, integral_add (integrable_finset_sum _ (fun j _ => hi j)) (h0.const_mul _),
    integral_finset_sum _ (fun j _ => hi j), integral_const_mul]
  exact h

theorem actual_locallyIntegrable (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (i : Fin 3) : LocallyIntegrable (fun x => response (ModalWeightedMode.coefficient n hn) z 1 u
      (VectorFourier.coordinateMap x) i) := by
  apply HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls
  intro T
  apply ((Lp.memLp (NewtonL2.physicalCoordinate
    (response (ModalWeightedMode.coefficient n hn) z 1 u) i)).restrict _).ae_eq
  exact ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae _ i)

#print axioms OQ14.ComplexSphereHelmholtz.actual_locallyIntegrable
#print axioms OQ14.ComplexSphereHelmholtz.actual_weak_helmholtz
end OQ14.ComplexSphereHelmholtz



