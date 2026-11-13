import Packet05GraphMetricFluxValues
import Packet05TensorCommutator

/-! Identify a compact smooth matrix extension with the actual graph flux
whenever the L² field is supported where the extension agrees with the chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphFluxExtension
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphMetricFlux
  OQ14.Packet05GraphMetricFluxValues OQ14.Packet05GraphChartMatrix OQ14.Packet05TensorCommutator
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem matrixField_ae (A : Fin 3 → Fin 3 → Test) (Q : L2Vector) (j : Fin 3) :
    (fun x => matrixField A Q j x) =ᵐ[volume]
      fun x => ∑ i : Fin 3, (A j i).function x * Q i x := by
  let X0 := scaleL2 (A j 0).function (A j 0).regular.continuous (A j 0).compact (Q 0)
  let X1 := scaleL2 (A j 1).function (A j 1).regular.continuous (A j 1).compact (Q 1)
  let X2 := scaleL2 (A j 2).function (A j 2).regular.continuous (A j 2).compact (Q 2)
  filter_upwards [Lp.coeFn_add X0 X1, Lp.coeFn_add (X0+X1) X2,
    scaleL2_ae (A j 0).function (A j 0).regular.continuous (A j 0).compact (Q 0),
    scaleL2_ae (A j 1).function (A j 1).regular.continuous (A j 1).compact (Q 1),
    scaleL2_ae (A j 2).function (A j 2).regular.continuous (A j 2).compact (Q 2)] with x h01 h012 h0 h1 h2
  change (X0+X1+X2 : L2Scalar) x = _
  rw [h012]
  simp only [Pi.add_apply]
  rw [h01]
  simp only [Pi.add_apply]
  change scaleL2 _ _ _ (Q 0) x + scaleL2 _ _ _ (Q 1) x + scaleL2 _ _ _ (Q 2) x = _
  rw [h0,h1,h2]
  simp [Fin.sum_univ_three]

theorem matrixField_eq_metricFlux (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (A : Fin 3 → Fin 3 → Test) (S : Set Space)
    (hQ : ∀ i, ∀ᵐ x ∂volume, x ∉ S → Q i x = 0)
    (hA : ∀ x ∈ S, ∀ j i, (A j i).function x =
      (metric (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j i : ℂ))
    (j : Fin 3) : matrixField A Q j = metricFlux g hg Q B hB j := by
  apply Lp.ext
  have hQall : ∀ᵐ x ∂volume, ∀ i, x ∉ S → Q i x = 0 := ae_all_iff.mpr hQ
  filter_upwards [matrixField_ae A Q j, metricFlux_ae g hg Q B hB j, hQall] with x ha hm hq
  rw [ha,hm]
  by_cases hx : x ∈ S
  · apply Finset.sum_congr rfl
    intro i _
    rw [hA x hx j i]
  · simp only [hq _ hx, mul_zero, Finset.sum_const_zero]

end OQ14.Packet05GraphFluxExtension
#print axioms OQ14.Packet05GraphFluxExtension.matrixField_ae
#print axioms OQ14.Packet05GraphFluxExtension.matrixField_eq_metricFlux
