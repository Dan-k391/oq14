import Packet06SphereInsertion
import Packet06SpherePolePersistence
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SphereInsertionPole
open Filter Set MeasureTheory Metric Packet06SectorOperator Packet06PhysicalNormalization
open scoped Topology

theorem fixed_contrast_pole_persistence (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z₀ = 0)
    (cone : StaticCoefficient.Coefficient)
    (hax : Packet06MaterialSymmetry.Axial cone) (hmer : Packet06MaterialSymmetry.Meridional cone)
    (hsupp : ∀ x : FourierL2.Space, x ∉ closedBall 0 1 → cone.value (VectorFourier.coordinateMap x) = 0)
    (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (hηb : ∀ j, η j ≤ 1)
    (ht : Tendsto η atTop (𝓝 0)) :
    ∃ (ψ : Sector →L[ℂ] ℂ) (z : ℕ → ℂ) (u : ℕ → Sector),
      ψ (numerator n hn z₀) = 1 ∧
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto u atTop (𝓝 (numerator n hn z₀)) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (Packet06SphereInsertion.family n hn cone η hη j) (z j) 1 T (u j)) atTop
        (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 T (numerator n hn z₀)))) ∧
      Tendsto (fun j => reciprocalNorm (Packet06SphereInsertion.family n hn cone η hη j) 1 (z j) (u j)) atTop
        (𝓝 (reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z₀ (numerator n hn z₀))) ∧
      (∀ᶠ j in atTop, z j ≠ 0 ∧ u j ≠ 0 ∧
        ComplexConvolutionAnalytic.volumeBlock (Packet06SphereInsertion.family n hn cone η hη j) (z j) 1 (u j) = 0 ∧ ψ (u j) = 1 ∧
        (∀ v : Sector, ComplexConvolutionAnalytic.volumeBlock (Packet06SphereInsertion.family n hn cone η hη j) (z j) 1 v = 0 ↔ v = ψ v • u j) ∧
        reciprocalNorm (Packet06SphereInsertion.family n hn cone η hη j) 1 (z j) (u j) ≠ 0 ∧
        Packet06ModePolePersistence.SimpleObservedPole (Packet06SphereInsertion.family n hn cone η hη j) 1 (z j) (u j)) := by
  obtain ⟨hb,hb₀,ha,hc,hax',hmer'⟩ := Packet06SphereInsertion.admissible n hn cone hax hmer hsupp η hη hηb ht
  exact Packet06SpherePolePersistence.actual_sphere_pole_persistence n hn hna z₀ hz₀ hdet
    (Packet06SphereInsertion.family n hn cone η hη) _ hb hb₀ ha hc hax' hmer'
#print axioms OQ14.Packet06SphereInsertionPole.fixed_contrast_pole_persistence
end OQ14.Packet06SphereInsertionPole
