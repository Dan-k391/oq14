import Packet06RoundedPeakFamily
import Packet06PhysicalAmplitudePeak
import Packet05RoundedModeMaximum

/-! One fixed normalized rounded family has actual Euclidean physical peaks
above every threshold, retaining both response and mode convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ActualPeakFamily
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum
open OQ14.Packet06SimpleCertificate (Certified)
open OQ14.Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem actual_peak_family {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z₀ : ℂ) (u₀ : Packet06SectorOperator.Sector)
    (hcert : Certified (sharp n hn g η hη) 1 z₀ u₀)
    (hN : reciprocalNorm (sharp n hn g η hη) 1 z₀ u₀=1)
    (hre : 0 < z₀.re) (him : z₀.im < 0) (Q : ℝ) (hQ : Q < z₀.re/(-2*z₀.im))
    (p : ConicalStaticVolume.Data) (hp : p.cutoff=g.datum.cutoff ∧ p.exponent<1)
    (s : Fin N → System p g.radius)
    (hE : ∀ i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius → totalCoordinate (s i) k x =
      Packet06ComplexElectric.electric z₀ (StaticCoefficient.sqrtMultiplier (sharp n hn g η hη) u₀)
        (DynamicVolume.source (sharp n hn g η hη) u₀) (x+g.center i) k)
    (hq : ∀ i, ConicalIntrinsicCoefficient.coefficient (s i) g.radius_pos
      (by rw [hp.1]; exact g.radius_inner) hp.2 ≠ 0)
    (r : ℝ) (hr : 0 < r) (hrb : r ≤ g.radius) :
    ∃ (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response (sharp n hn g η hη) z₀ 1 T u₀))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i,
        0 < (volume.restrict (closedBall (g.center i) r)) {x | M <
          physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
            (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
            (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x} := by
  obtain ⟨z,v,coord,hz,hv,hresp,hgood,hpeak⟩ :=
    Packet06RoundedPeakFamily.rounded_peak_family n hn g η hη z₀ u₀ hcert hN hre him Q hQ
      p hp s hE hq r hr hrb
  refine ⟨z,v,hz,hv,hresp,hgood,?_⟩
  intro M
  filter_upwards [hpeak M] with j hpj i
  have hball : closedBall (g.center i) r ⊆ ball (0 : Maxwell.Space) 1 :=
    (closedBall_subset_closedBall (hrb.trans g.radius_outer)).trans (g.outer_inside i)
  have hactual := Packet06PhysicalAmplitudePeak.actual_response_peak (rounded n hn g η hη j)
    (z j) 1 1 (v j) (Packet05RoundedModeSupport.rounded_support n hn g η hη j)
    (ball (g.center i) r) (ball_subset_closedBall.trans (hball.trans ball_subset_closedBall))
    (coord i) M (hpj i)
  have hclosed := hactual.trans_le
    (Measure.restrict_mono_set volume (ball_subset_closedBall : ball (g.center i) r ⊆ closedBall (g.center i) r) _)
  exact hclosed

end OQ14.Packet06ActualPeakFamily
#print axioms OQ14.Packet06ActualPeakFamily.actual_peak_family
