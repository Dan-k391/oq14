import NewtonL2
import WeakPoynting.PartialSmoothing

/-! # The actual Newton response has zero distributional curl

The existing compact C1 weak-curl relation is proved for every L2 source,
using actual Fourier pairings and the proved compact-test approximation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.NewtonWeak

open MeasureTheory OQ14.NewtonL2 OQ14.Maxwell
open scoped SchwartzMap FourierTransform

abbrev Space := Maxwell.Space

theorem projected_fourier_ae (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (VectorFourier.fourier (VectorFourier.physicalProjection F)) i
      =ᵐ[volume] fun ξ => -(∑ j, NewtonHessian.hessianSymbol ξ i j *
        VectorFourier.fourier F (VectorFourier.coordinateMap ξ) j) := by
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (NewtonHessian.physicalProjection_hessianSymbol F i)
  filter_upwards [physicalCoordinate_ae
    (VectorFourier.fourier (VectorFourier.physicalProjection F)) i, hp] with ξ hx hy
  rw [hx, hy, MeasurableEquiv.symm_apply_apply]

theorem newton_fourier_ae (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (VectorFourier.fourier (newtonOperator F)) i
      =ᵐ[volume] fun ξ => ∑ j, NewtonHessian.hessianSymbol ξ i j *
        VectorFourier.fourier F (VectorFourier.coordinateMap ξ) j := by
  have he : VectorFourier.fourier (newtonOperator F) =
      -VectorFourier.fourier (VectorFourier.physicalProjection F) := by
    change VectorFourier.fourier (-VectorFourier.physicalProjection F) = _
    exact map_neg _ _
  rw [he, physicalCoordinate_neg]
  filter_upwards [Lp.coeFn_neg
    (physicalCoordinate (VectorFourier.fourier (VectorFourier.physicalProjection F)) i),
    projected_fourier_ae F i] with ξ hx hy
  rw [hx]
  simp only [Pi.neg_apply, hy, neg_neg]

theorem symbol_cross_cancel (ξ : Space) (i j l : Fin 3) :
    NewtonHessian.hessianSymbol ξ i l * (ξ j : ℂ) =
      NewtonHessian.hessianSymbol ξ j l * (ξ i : ℂ) := by
  unfold NewtonHessian.hessianSymbol
  ring

/-- Actual mixed test pairings of the spatial Newton response are symmetric. -/
theorem newton_mixed_pairing (F : VectorL2) (f : 𝓢(Space, ℂ)) (i j : Fin 3) :
    (∫ x, physicalCoordinate (newtonOperator F) i x * dcoord f x j) =
      ∫ x, physicalCoordinate (newtonOperator F) j x * dcoord f x i := by
  change (∫ x, physicalCoordinate (newtonOperator F) i x *
    (GradientProjection.pderivative j f) x) =
      ∫ x, physicalCoordinate (newtonOperator F) j x *
        (GradientProjection.pderivative i f) x
  rw [scalar_bilinear_parseval (physicalCoordinate (newtonOperator F) i)
      (GradientProjection.pderivative j f),
    scalar_bilinear_parseval (physicalCoordinate (newtonOperator F) j)
      (GradientProjection.pderivative i f),
    ← physicalCoordinate_fourier, ← physicalCoordinate_fourier]
  apply integral_congr_ae
  filter_upwards [newton_fourier_ae F i, newton_fourier_ae F j] with ξ hi hj
  rw [hi, hj, NewtonHessian.inverse_fourier_pderivative,
    NewtonHessian.inverse_fourier_pderivative, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  have h := symbol_cross_cancel ξ i j l
  linear_combination VectorFourier.fourier F (VectorFourier.coordinateMap ξ) l *
    (-(2 * Real.pi * Complex.I)) *
    ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ * h

def response (F : VectorL2) : WeakCurl.L2Vector :=
  fun i => physicalCoordinate (newtonOperator F) i

theorem newton_hasWeakCurl_zero (F : VectorL2) :
    WeakCurl.HasWeakCurl (response F) 0 := by
  apply PartialSmoothing.hasWeakCurl_of_schwartz_integral
  intro f j
  change (∫ x, (0 : WeakCurl.L2Scalar) x * f x) =
    (∫ x, physicalCoordinate (newtonOperator F) (WeakCurl.next j) x *
      dcoord f x (WeakCurl.previous j)) -
    (∫ x, physicalCoordinate (newtonOperator F) (WeakCurl.previous j) x *
      dcoord f x (WeakCurl.next j))
  rw [newton_mixed_pairing, sub_self]
  simp

end OQ14.NewtonWeak

#print axioms OQ14.NewtonWeak.projected_fourier_ae
#print axioms OQ14.NewtonWeak.newton_fourier_ae
#print axioms OQ14.NewtonWeak.symbol_cross_cancel
#print axioms OQ14.NewtonWeak.newton_mixed_pairing
#print axioms OQ14.NewtonWeak.newton_hasWeakCurl_zero
