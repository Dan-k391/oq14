import Packet06RoundedIntrinsicPeaks

/-! One fixed normalized rounded mode family has every prescribed large-field
threshold eventually, while retaining its actual response convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedPeakFamily
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalRounding
open OQ14.Packet06SimpleCertificate (Certified)
open OQ14.Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem rounded_peak_family {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
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
    ∃ (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (coord : Fin N → Fin 3),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response (sharp n hn g η hη) z₀ 1 T u₀))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i, 0 < (volume.restrict (ball (g.center i) r)) {x | M <
          ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 1 (v j)) (coord i) x‖} := by
  obtain ⟨z,v,hz,hv,hresp,hgood⟩ := same_mode_rounding n hn g η hη z₀ u₀ hcert hN hre him Q hQ
  have hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 →
      (sharp n hn g η hη).value (VectorFourier.coordinateMap x) = 0 :=
    Packet06ContrastInsertion.support _ _ η hη 1 (ModalWeightedMode.coefficient_support n hn) (admissible g).2.2
  have hunbounded (i : Fin N) : ∃ k : Fin 3, ¬∃ B : ℝ, ∀ᵐ x : Maxwell.Space ∂volume.restrict (ball (g.center i) r),
      ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (sharp n hn g η hη) z₀ 1 1 u₀) k x‖ ≤ B := by
    apply Packet06RoundedIntrinsicPeaks.sharp_coordinate_unbounded (sharp n hn g η hη) z₀ u₀ hsupp p g.radius g.radius_pos
      (by rw [hp.1]; exact g.radius_inner) hp.2 (s i) (g.center i) _ (hE i) (hq i) r hr hrb
    intro x hx
    exact ball_subset_closedBall ((Packet06ConcreteExcitation.local_geometry g i).1 x (ball_subset_closedBall hx))
  let coord : Fin N → Fin 3 := fun i => Classical.choose (hunbounded i)
  have hcoord (i : Fin N) := Classical.choose_spec (hunbounded i)
  have hpeak (M : ℝ) (i : Fin N) : ∀ᶠ j in atTop,
      0 < (volume.restrict (ball (g.center i) r)) {x | M <
        ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 1 (v j)) (coord i) x‖} := by
    have hlim := ((ConicalVolumePeaks.physicalCoordinateCLM (coord i)).continuous.tendsto _).comp (hresp 1 (by norm_num))
    exact L2PeakPreservation.eventually_positive_superlevel _ _ _ hlim (hcoord i) M
  exact ⟨z,v,coord,hz,hv,hresp,hgood,fun M => Filter.eventually_all.mpr (hpeak M)⟩

end OQ14.Packet06RoundedPeakFamily
#print axioms OQ14.Packet06RoundedPeakFamily.rounded_peak_family
