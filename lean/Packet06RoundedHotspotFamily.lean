import Packet05ActualUniformCollar
import Packet06CollaredHotspotFamily
import Packet06ActualPeakFamily
import Packet06RoundedPeakFamily
import Packet06PhysicalAmplitudePeak
import Packet05RoundedModeMaximum

/-! A fixed normalized rounded mode family has actual isolated meridional
hotspots above every threshold and uniformly bounded open physical collars. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedHotspotFamily
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum
open OQ14.Packet06SimpleCertificate (Certified)
open OQ14.Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem rounded_hotspot_family {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
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
    (r : ℝ) (hr : 0 < r) (hrb : r < g.radius) :
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
      ∃ (A : Fin N → Set Maxwell.Space) (B : ℝ), 0 ≤ B ∧
        (∀ i, IsOpen (A i) ∧ A i ⊆ ball (g.center i) g.radius ∧ sphere (g.center i) r ⊆ A i) ∧
        (∀ᶠ j in atTop, ∀ i, ∀ᵐ x ∂volume.restrict (A i),
          physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
            (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
            (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x ≤ B) ∧
        ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i,
          Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη j) (z j) (v j)
            (body g j) (g.center i) r M B := by
  obtain ⟨z,v,hz,hv,hresp,hgood,hpeak⟩ :=
    Packet06ActualPeakFamily.actual_peak_family n hn g η hη z₀ u₀ hcert hN hre him Q hQ
      p hp s hE hq r hr hrb.le
  have hz0 : ∀ᶠ j in atTop, z j ≠ 0 := by
    filter_upwards [hgood] with j hj
    intro he
    have hh := hj.1
    rw [he] at hh
    simp at hh
  have hmode : ∀ᶠ j in atTop,
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0 := by
    filter_upwards [hgood] with j hj
    obtain ⟨w,ψ,_,hk,_,_⟩ := hj.2.2.2.1
    exact hk
  refine ⟨z,v,hz,hv,hresp,hgood,?_⟩
  exact Packet06CollaredHotspotFamily.collared_hotspots_of_uniform_collars n hn g η hη z v r hr hrb
    (hz0.and hmode)
    (fun i => Packet05ActualUniformCollar.actual_uniform_collar n hn g η hη z v z₀ u₀ hz hv hz0 hmode i r hr hrb)
    hpeak

end OQ14.Packet06RoundedHotspotFamily
#print axioms OQ14.Packet06RoundedHotspotFamily.rounded_hotspot_family
