import Packet06ConeZeroProjection
import WeakPoynting.Translations
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06AngularPairLimit
open Filter MeasureTheory OQ14.WeakCurl OQ14.WeakGreen
open scoped Topology InnerProductSpace

theorem scalar_pair_tendsto (u v : ℕ → L2Scalar) (u₀ v₀ : L2Scalar)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun j => scalarProduct (u j) (v j)) atTop (𝓝 (scalarProduct u₀ v₀)) := by
  have hconj := (((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 volume).continuous.tendsto u₀).comp hu
  simpa only [scalarProduct,innerSL_apply,ContinuousLinearMap.compLpL] using hconj.inner hv
#print axioms OQ14.Packet06AngularPairLimit.scalar_pair_tendsto
end OQ14.Packet06AngularPairLimit
