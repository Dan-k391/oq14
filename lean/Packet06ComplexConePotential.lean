import Packet06ComplexElectric
import ConicalTranslatedPotential
import ConicalProjectionLocalization
import NewtonReciprocity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexConePotential
open MeasureTheory Metric OQ14.Maxwell
open OQ14.ConicalGradientGraph (PotentialData)

def potentialData (z : ℂ) (S : ℝ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j) : PotentialData where
  potential := Packet06ComplexPotential.potential z ρ
  derivative i x := Packet06ComplexElectric.electric z F ρ x i-Packet06ComplexPotential.correction z ρ x i
  potential_memLp R := Packet06ComplexPotential.potential_memLp_ball z R S F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF) hc hF
  derivative_memLp R i := (Packet06ComplexElectric.electric_memLp_ball z R S F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF) hc hF i).sub
      (Packet06ComplexPotential.correction_memLp_ball z R S F ρ
        (NewtonReciprocity.compact_source_integrable S F ρ hc hF) hc hF i)
  weak := Packet06ComplexElectric.potential_weak_partial z F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF)
    (fun j => HasCompactSupport.intro' (isCompact_closedBall (0 : Space) S) isClosed_closedBall (hc j)) hF

#print axioms OQ14.Packet06ComplexConePotential.potentialData
end OQ14.Packet06ComplexConePotential
