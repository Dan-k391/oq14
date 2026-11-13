import Packet06ModeExcitation
import Packet06ComplexElectric
import Packet06SphereScaledLocal
import ConicalBallRestriction
import StaticBallTranslation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06CenteredBall
open MeasureTheory Metric OQ14.Maxwell
open scoped Topology
abbrev V := VectorFourier.VectorL2

def restrict (b : ℝ) (center : Maxwell.Space) : V →L[ℂ] ConicalRungeBall.BallL2 b :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ConicalRungeBall.ScalarBall b)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => (ConicalBallRestriction.scalar b).comp
      ((StaticBallTranslation.scalar (-center)).toContinuousLinearMap.comp (DynamicConvolution.component j))))

theorem restrict_ae (b : ℝ) (center : Maxwell.Space) (F : V) (i : Fin 3) :
    (restrict b center F i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)]
      fun x => F (VectorFourier.coordinateMap (x+center)) i := by
  have htrans := StaticBallTranslation.scalar_ae (-center) (NewtonL2.physicalCoordinate F i)
  have hcoord := (measurePreserving_add_right (volume : Measure Maxwell.Space) center).quasiMeasurePreserving.ae
    (NewtonL2.physicalCoordinate_ae F i)
  have hr := ConicalBallRestriction.scalarRestriction_ae b
    (StaticBallTranslation.scalar (-center) (NewtonL2.physicalCoordinate F i))
  filter_upwards [hr,ae_restrict_of_ae htrans,ae_restrict_of_ae hcoord] with x hx ht hc
  change ConicalBallRestriction.scalarRestriction b (StaticBallTranslation.scalar (-center)
    (NewtonL2.physicalCoordinate F i)) x = _ at hx
  change ConicalBallRestriction.scalarRestriction b (StaticBallTranslation.scalar (-center)
    (NewtonL2.physicalCoordinate F i)) x = _
  rw [hx,ht]
  simpa only [sub_neg_eq_add] using hc

theorem restrict_tendsto (b : ℝ) (center : Maxwell.Space) (F : ℕ → V) (F₀ : V)
    (hF : Filter.Tendsto F Filter.atTop (𝓝 F₀)) :
    Filter.Tendsto (fun j => restrict b center (F j)) Filter.atTop (𝓝 (restrict b center F₀)) :=
  ((restrict b center).continuous.tendsto F₀).comp hF
theorem restrict_response_actual (b : ℝ) (center : Maxwell.Space) (c : StaticCoefficient.Coefficient)
    (z : ℂ) (S T : ℝ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hball : ∀ x ∈ closedBall (0 : Maxwell.Space) b, x+center ∈ closedBall 0 T) (i : Fin 3) :
    (restrict b center (ComplexExteriorResponse.response c z S T u) i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)]
      fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (x+center) i := by
  have he := Packet06ComplexElectric.electric_ae_on_ball z S T (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i
  have he' := (ae_restrict_iff' measurableSet_closedBall).mp he
  have hshift := (measurePreserving_add_right (volume : Measure Maxwell.Space) center).quasiMeasurePreserving.ae he'
  filter_upwards [restrict_ae b center (ComplexExteriorResponse.response c z S T u) i,
    ae_restrict_of_ae hshift,ae_restrict_mem measurableSet_closedBall] with x hx he hxball
  rw [hx]
  exact he (hball x hxball)
theorem restrict_sphere_base (b : ℝ) (center : Maxwell.Space) (n : ℝ) (hn : 1 < n) (z a : ℂ)
    (hz : z ≠ 0) (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T)
    (hball : ∀ x ∈ closedBall (0 : Maxwell.Space) b, x+center ∈ ball 0 1) (i : Fin 3) :
    (restrict b center (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z 1 T
      (a • (Packet06SectorOperator.numerator n hn z : V))) i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)]
      fun x => Packet06SphereLocalField.inner n z a (center+x) i := by
  let F := Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z 1 T
      (a • (Packet06SectorOperator.numerator n hn z : V))
  have he := Packet06SphereScaledLocal.response_inner_scaled_ae n hn z a hz hdet T hT i
  have he' := (ae_restrict_iff' measurableSet_ball).mp he
  have hshift := (measurePreserving_add_right (volume : Measure Maxwell.Space) center).quasiMeasurePreserving.ae he'
  filter_upwards [restrict_ae b center F i,ae_restrict_of_ae hshift,
    ae_restrict_mem measurableSet_closedBall] with x hx he hxball
  rw [hx]
  simpa only [add_comm] using he (hball x hxball)
#print axioms OQ14.Packet06CenteredBall.restrict_ae
#print axioms OQ14.Packet06CenteredBall.restrict_tendsto
#print axioms OQ14.Packet06CenteredBall.restrict_response_actual
#print axioms OQ14.Packet06CenteredBall.restrict_sphere_base
end OQ14.Packet06CenteredBall
