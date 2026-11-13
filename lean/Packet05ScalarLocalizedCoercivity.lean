import Packet05ScalarPrincipalLocalization
import Packet05GraphMetricFlux

/-! The actual square-cutoff principal term is quantitatively coercive when
the smooth matrix extension agrees with the graph metric on the cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarLocalizedCoercivity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphMetricFlux
  OQ14.Packet05TensorCommutator OQ14.Packet05GraphFluxExtension OQ14.Packet05ScalarPrincipalLocalization
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem localized_principal_coercivity (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test) (Q : L2Vector)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (hA : ∀ x ∈ tsupport ζ.function, ∀ j i, (A j i).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j i : ℂ)) (d : ℝ) (hd : 0 ≤ d) :
    ‖cutVector ζ Q 0‖^2 + ‖cutVector ζ Q 1‖^2 + ‖cutVector ζ Q 2‖^2 ≤ (2+4*M^2) *
      (∑ j : Fin 3, scalarProduct (mulWeight d hd (matrixField A Q j))
        (conjScalar (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
          (squareTest ζ).complexTest.compact (Q j)))).re := by
  have hQ (i : Fin 3) : ∀ᵐ x ∂volume, x ∉ tsupport ζ.function → cutVector ζ Q i x = 0 := by
    filter_upwards [cutVector_ae ζ Q i] with x hx hn
    rw [hx, image_eq_zero_of_nmem_tsupport hn]
    simp
  have hm (j : Fin 3) : matrixField A (cutVector ζ Q) j = metricFlux g hg (cutVector ζ Q) B hB j :=
    matrixField_eq_metricFlux g hg (cutVector ζ Q) B hB A (tsupport ζ.function) hQ hA j
  have he : (∑ j : Fin 3, scalarProduct (mulWeight d hd (matrixField A Q j))
      (conjScalar (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
        (squareTest ζ).complexTest.compact (Q j)))) =
      ∑ j : Fin 3, scalarProduct (mulWeight d hd (metricFlux g hg (cutVector ζ Q) B hB j))
        (conjScalar (cutVector ζ Q j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [square_cutoff_principal_pairing ζ A Q d hd j, hm j]
  rw [he]
  exact metric_flux_coercivity g hg (cutVector ζ Q) M hM B hB d hd

end OQ14.Packet05ScalarLocalizedCoercivity
#print axioms OQ14.Packet05ScalarLocalizedCoercivity.localized_principal_coercivity
