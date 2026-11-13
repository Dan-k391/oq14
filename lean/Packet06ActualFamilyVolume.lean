import Packet06PlacedRoundedVolumeLimits

/-! The actual constructed normalized modal family has diverging attained
one-sided electric maxima and vanishing physical mode volumes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06ActualFamilyVolume
open MeasureTheory Metric Set Filter Maxwell ConicalProjectionData
  Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet05ActualMaximum
  Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits
open scoped Topology

theorem actual_family_volume {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z₀ : ℂ) (u₀ : Packet06SectorOperator.Sector)
    (hcert : Packet06SimpleCertificate.Certified (sharp n hn g η hη) 1 z₀ u₀)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (sharp n hn g η hη) 1 z₀ u₀=1)
    (hre : 0 < z₀.re) (him : z₀.im < 0) (Q : ℝ) (hQ : Q < z₀.re/(-2*z₀.im))
    (p : ConicalStaticVolume.Data) (hp : p.cutoff=g.datum.cutoff ∧ p.exponent<1)
    (s : Fin N → System p g.radius)
    (hE : ∀ i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius → totalCoordinate (s i) k x =
      Packet06ComplexElectric.electric z₀ (StaticCoefficient.sqrtMultiplier (sharp n hn g η hη) u₀)
        (DynamicVolume.source (sharp n hn g η hη) u₀) (x+g.center i) k)
    (hq : ∀ i, ConicalIntrinsicCoefficient.coefficient (s i) g.radius_pos
      (by rw [hp.1]; exact g.radius_inner) hp.2 ≠ 0)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrg : r ≤ g.radius)
    (K : ℝ) (hK : 1 < K) (hceil : (1+η)*n^2 ≤ K^2) :
    ∃ (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (d : ℕ → MaximumData),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      (∀ᶠ j in atTop, Valid n hn g η hη (z j) (v j) j i r (d j)) ∧
      Tendsto (fun j => amplitude (vector (d j))) atTop atTop ∧
      Tendsto (fun j => 1/(MaterialMaxwell.dielectric (rounded n hn g η hη j) (d j).point *
        (amplitude (vector (d j)))^2)) atTop (𝓝 0) ∧
      ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, vector (d (φ j)) k ≠ 0) ∧
        Tendsto (fun j => (((MaterialMaxwell.dielectric (rounded n hn g η hη (φ j)) (d (φ j)).point : ℝ) : ℂ)*
          (vector (d (φ j)) k)^2)⁻¹) atTop (𝓝 0) := by
  obtain ⟨z,v,hz,hv,hresp,hgood,hpeak⟩ := Packet06ActualPeakFamily.actual_peak_family
    n hn g η hη z₀ u₀ hcert hN hre him Q hQ p hp s hE hq r hr hrg
  have hz0 : ∀ᶠ j in atTop, z j ≠ 0 := by
    filter_upwards [hgood] with j hj
    exact fun h => by have := hj.1; rw [h] at this; simp at this
  have hm : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0 := by
    filter_upwards [hgood] with j hj
    obtain ⟨w,ψ,_,hk,_,_⟩ := hj.2.2.2.1
    exact hk
  have hp' (M : ℝ) := (hpeak M).mono (fun j hj => hj i)
  obtain ⟨d,hd,hdiv,hvol,hdir⟩ := actual_rounded_maximum_volume n hn g η hη z v hz0 hm i r hr hrg hp' K hK hceil
  exact ⟨z,v,d,hz,hv,hgood,hd,hdiv,hvol,hdir⟩
end OQ14.Packet06ActualFamilyVolume
#print axioms OQ14.Packet06ActualFamilyVolume.actual_family_volume
