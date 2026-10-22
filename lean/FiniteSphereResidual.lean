import FiniteSphereStatic
import StaticSphereResidual

/-! # Actual material residual of finite isolated-sphere trials -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.FiniteSphereResidual

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residual (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) (E : ι → Vector) : VectorL2 :=
  StaticNewton.volumeBlock (coefficient p r χ hχ) (trial p r χ E)-forcing p r χ E

theorem residual_on_ball (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (hr : ∀ j, 0 < r j)
    (hsep : ∀ i j, i ≠ j → r i+r j ≤ dist (p i) (p j)) (i : ι) (m : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (p i) (r i) →
      residual p r χ hχ E (VectorFourier.coordinateMap x) m =
        -(Real.sqrt χ : ℂ) * NewtonL2.newtonOperator
          (StaticBallInteraction.crossSource p r (fun j => StaticSpherePolarization.polarization χ (E j)) i)
            (VectorFourier.coordinateMap x) m := by
  let v := trial p r χ E
  let f₀ := forcing p r χ E
  let P := fun j => StaticSpherePolarization.polarization χ (E j)
  let u₀ := StaticBallCentered.source (p i) (r i) (P i)
  let uc := StaticBallInteraction.crossSource p r P i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (StaticNewton.volumeBlock (coefficient p r χ hχ) v) f₀)
  have hb := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticNewton.volumeBlock_ae (coefficient p r χ hχ) v)
  have ha := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (NewtonL2.newtonOperator u₀) (NewtonL2.newtonOperator uc))
  have he : StaticNewton.response (coefficient p r χ hχ) v =
      NewtonL2.newtonOperator u₀+NewtonL2.newtonOperator uc := by
    change NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier _ _) = _
    rw [physical_trial p r χ hχ E, sumSource_eq_self_cross p r P i, map_add]
  filter_upwards [hs, hb, ha,
    sumSource_on_ball p r (fun j => StaticSphereMaterial.trialVector χ (E j)) hsep i m,
    sumSource_on_ball p r (fun j => (Real.sqrt χ : ℂ) • E j) hsep i m,
    StaticBallCentered.newton_source_interior (p i) (r i) (hr i) (P i) m]
    with x hs hb ha hv hf hn hm
  have hu : x ∈ ⋃ j, ball (p j) (r j) := mem_iUnion.mpr ⟨i, hm⟩
  change residual p r χ hχ E (VectorFourier.coordinateMap x) m = _
  change (StaticNewton.volumeBlock (coefficient p r χ hχ) v-f₀)
    (VectorFourier.coordinateMap x) m = _
  rw [hs, Pi.sub_apply, hb]
  change v (VectorFourier.coordinateMap x) m -
    (Real.sqrt ((coefficient p r χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
      StaticNewton.response (coefficient p r χ hχ) v (VectorFourier.coordinateMap x) m -
    f₀ (VectorFourier.coordinateMap x) m = _
  specialize hv hm
  specialize hf hm
  change v (VectorFourier.coordinateMap x) m = _ at hv
  change f₀ (VectorFourier.coordinateMap x) m = _ at hf
  rw [hv, hf, coefficient_value, if_pos hu, he, ha]
  change StaticSphereMaterial.trialVector χ (E i) m -
    (Real.sqrt χ : ℂ)*(NewtonL2.newtonOperator u₀ (VectorFourier.coordinateMap x) m +
      NewtonL2.newtonOperator uc (VectorFourier.coordinateMap x) m) -
    (Real.sqrt χ : ℂ)*E i m = _
  rw [show NewtonL2.newtonOperator u₀ (VectorFourier.coordinateMap x) m = -P i m/3 from hn hm]
  change StaticSphereMaterial.trialVector χ (E i) m -
    (Real.sqrt χ : ℂ)*(-StaticSpherePolarization.polarization χ (E i) m/3 +
      NewtonL2.newtonOperator uc (VectorFourier.coordinateMap x) m) -
    (Real.sqrt χ : ℂ)*E i m = _
  have ht := StaticSphereMaterial.trial_scalar_identity χ hχ (E i) m
  linear_combination ht

theorem residual_outside (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (m : Fin 3) :
    ∀ᵐ x : Space, x ∉ ⋃ j, ball (p j) (r j) →
      residual p r χ hχ E (VectorFourier.coordinateMap x) m = 0 := by
  let v := trial p r χ E
  let f₀ := forcing p r χ E
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (StaticNewton.volumeBlock (coefficient p r χ hχ) v) f₀)
  have hb := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticNewton.volumeBlock_ae (coefficient p r χ hχ) v)
  filter_upwards [hs, hb,
    sumSource_ae p r (fun j => StaticSphereMaterial.trialVector χ (E j)) m,
    sumSource_ae p r (fun j => (Real.sqrt χ : ℂ) • E j) m]
    with x hs hb hv hf hx
  have hn : ∀ j : ι, x ∉ ball (p j) (r j) := fun j hj => hx (mem_iUnion.mpr ⟨j,hj⟩)
  change v (VectorFourier.coordinateMap x) m = _ at hv
  change f₀ (VectorFourier.coordinateMap x) m = _ at hf
  change (StaticNewton.volumeBlock (coefficient p r χ hχ) v-f₀)
    (VectorFourier.coordinateMap x) m = _
  rw [hs, Pi.sub_apply, hb]
  change v (VectorFourier.coordinateMap x) m -
    (Real.sqrt ((coefficient p r χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
      StaticNewton.response (coefficient p r χ hχ) v (VectorFourier.coordinateMap x) m -
    f₀ (VectorFourier.coordinateMap x) m = 0
  rw [coefficient_value, if_neg hx, hv, hf]
  simp [hn]

end OQ14.FiniteSphereResidual

#print axioms OQ14.FiniteSphereResidual.residual_on_ball
#print axioms OQ14.FiniteSphereResidual.residual_outside
