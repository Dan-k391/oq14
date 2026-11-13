import Packet05GivenTraceCollar
import Packet06PlacedTraceCollar

/-! Actual one-sided continuous electric branches and a pointwise amplitude
bound on an open collar, packaged for the final family selection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05OneSidedCollar
open MeasureTheory Set Metric Filter Maxwell Packet06ConcreteModalRounding Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

def OneSidedCollar (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (body A : Set Space) (B : ℝ) : Prop :=
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
  ∃ inside outside : Fin 3 → Space → ℂ,
    (∀ k, ContinuousOn (inside k) (A ∩ closure body)) ∧
    (∀ k, ContinuousOn (outside k) (A ∩ closure (closure body)ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (A ∩ body)] inside k) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (A ∩ (closure body)ᶜ)] outside k) ∧
    ∀ phase x, x ∈ A ∩ phaseDomain body phase → physicalAmplitude (phaseField inside outside phase) x ≤ B

theorem given_collar_eventually {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (i : Fin N) (A : Set Space) (B : ℝ) (hA : IsOpen A) (hAr : A ⊆ ball (g.center i) g.radius)
    (hbound : ∀ᶠ j in atTop, ∀ᵐ y ∂volume.restrict A,
      physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) y ≤ B) :
    ∀ᶠ j in atTop, OneSidedCollar (rounded n hn g η hη j) (z j) (v j) (body g j) A B := by
  have h := Packet05GivenTraceCollar.given_uniform_trace_collar n hn g η hη z v hz hmode i A B hA hAr hbound
  filter_upwards [h] with j hj
  obtain ⟨inside,outside,hin,hout,hiae,hoae,htrace⟩ := hj
  have hAK : A ⊆ closedBall (g.center i) g.radius := hAr.trans ball_subset_closedBall
  refine ⟨inside,outside,?_,?_,?_,?_,htrace⟩
  · exact fun k => (hin k).mono (inter_subset_inter_left _ hAK)
  · exact fun k => (hout k).mono (inter_subset_inter_left _ hAK)
  · exact fun k => ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hAK) (hiae k)
  · exact fun k => ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hAK) (hoae k)

end OQ14.Packet05OneSidedCollar
#print axioms OQ14.Packet05OneSidedCollar.given_collar_eventually
