import Packet05OneSidedCollar

/-! The selected finite set of given physical collars all retain their
one-sided traces for one common late mode index. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GivenAllCollars
open MeasureTheory Set Metric Filter Maxwell Packet06ConcreteModalRounding Packet05ActualMaximum Packet05OneSidedCollar
open scoped Topology
abbrev Space := Maxwell.Space

theorem given_all_collars_eventually {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (A : Fin N → Set Space) (B : Fin N → ℝ) (hA : ∀ i, IsOpen (A i))
    (hAr : ∀ i, A i ⊆ ball (g.center i) g.radius)
    (hbound : ∀ i, ∀ᶠ j in atTop, ∀ᵐ y ∂volume.restrict (A i),
      physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) y ≤ B i) :
    ∀ᶠ j in atTop, ∀ i, OneSidedCollar (rounded n hn g η hη j) (z j) (v j) (body g j) (A i) (B i) := by
  apply Filter.eventually_all.mpr
  intro i
  exact given_collar_eventually n hn g η hη z v hz hmode i (A i) (B i) (hA i) (hAr i) (hbound i)

end OQ14.Packet05GivenAllCollars
#print axioms OQ14.Packet05GivenAllCollars.given_all_collars_eventually
