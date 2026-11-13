import Packet06SmallClusterExcited
import ConicalFixedInputTransfer
import ConicalVolumePeaks
import L2PeakPreservation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06IntrinsicPeaks
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
open scoped Topology

theorem unbounded_component (p : ConicalStaticVolume.Data) (b : ℝ) (hb : 0 < b)
    (hbi : b < p.cutoff.rIn) (hν : p.exponent < 1) (s : System p b)
    (E : Field) (hE : ∀ i, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 b → totalCoordinate s i x=E x i)
    (hq : ConicalIntrinsicCoefficient.coefficient s hb hbi hν ≠ 0)
    (G : Fin 3 → FourierL2.ScalarL2)
    (hG : ∀ i, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 b → G i x = E x i)
    (r : ℝ) (hr : 0 < r) (hrb : r ≤ b) :
    ∃ i : Fin 3, ¬∃ M : ℝ, ∀ᵐ x : Maxwell.Space ∂volume.restrict (ball 0 r), ‖G i x‖ ≤ M := by
  have hu := ConicalFixedInputTransfer.not_essentially_bounded p b hν s E hE _ hq
    (ConicalIntrinsicCoefficient.coefficient_spec s hb hbi hν) r hr hrb
  obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded E (ball 0 r) hu
  refine ⟨i,?_⟩
  rintro ⟨M,hM⟩
  apply hi
  refine ⟨M,?_⟩
  filter_upwards [hM,ae_restrict_of_ae (hG i),ae_restrict_mem measurableSet_ball] with x hm hg hx
  rw [← hg (ball_subset_ball hrb hx)]
  exact hm

theorem rounded_positive (p : ConicalStaticVolume.Data) (b : ℝ) (hb : 0 < b)
    (hbi : b < p.cutoff.rIn) (hν : p.exponent < 1) (s : System p b)
    (E : Field) (hE : ∀ i, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 b → totalCoordinate s i x=E x i)
    (hq : ConicalIntrinsicCoefficient.coefficient s hb hbi hν ≠ 0)
    (G : ℕ → Fin 3 → FourierL2.ScalarL2) (G₀ : Fin 3 → FourierL2.ScalarL2)
    (hlim : ∀ i, Tendsto (fun j => G j i) atTop (𝓝 (G₀ i)))
    (hG : ∀ i, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 b → G₀ i x = E x i)
    (r : ℝ) (hr : 0 < r) (hrb : r ≤ b) (M : ℝ) :
    ∃ i : Fin 3, ∀ᶠ j in atTop,
      0 < (volume.restrict (ball (0 : Maxwell.Space) r)) {x | M < ‖G j i x‖} := by
  obtain ⟨i,hi⟩ := unbounded_component p b hb hbi hν s E hE hq G₀ hG r hr hrb
  exact ⟨i,L2PeakPreservation.eventually_positive_superlevel _ _ _ (hlim i) hi M⟩
#print axioms OQ14.Packet06IntrinsicPeaks.unbounded_component
#print axioms OQ14.Packet06IntrinsicPeaks.rounded_positive
end OQ14.Packet06IntrinsicPeaks
