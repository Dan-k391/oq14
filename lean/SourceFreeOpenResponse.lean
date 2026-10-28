import ExteriorMaterialOffCarrier
import CompactResponseSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceFreeOpenResponse
open MeasureTheory Metric Set OQ14.Maxwell

 theorem electric_smooth (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y = 0)
    (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ExteriorContinuity.electric k ρ y i) U := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro j _
  exact CompactResponseSmooth.response_contDiffAt _ _ (ExteriorSmooth.dyadic_contDiffAt k i j)
    (hρ j) (hc j) x (ExteriorMaterialOffCarrier.source_excluded_open (ρ j) U hU (hi j) x hx)

 theorem electric_ae (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y = 0) :
    ∀ᵐ x : Space, x ∈ U → FieldResponse.electric k F ρ x = ExteriorContinuity.electric k ρ x := by
  filter_upwards [ae_all_iff.mpr (fun i => ExteriorMaterialOffCarrier.electric_ae_open k F ρ hρ hF S hc U hU hi i)] with x hx hxU
  exact funext (fun i => hx i hxU)
end OQ14.SourceFreeOpenResponse
#print axioms OQ14.SourceFreeOpenResponse.electric_smooth
#print axioms OQ14.SourceFreeOpenResponse.electric_ae
