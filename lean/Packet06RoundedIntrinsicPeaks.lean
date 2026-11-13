import Packet06IntrinsicPeaks
import Packet06ConcreteModalRounding
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedIntrinsicPeaks
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalRounding
open OQ14.Packet06SimpleCertificate (Certified)
open OQ14.Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem sharp_coordinate_unbounded (c : StaticCoefficient.Coefficient) (z : ℂ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x) = 0)
    (p : ConicalStaticVolume.Data) (b : ℝ) (hb : 0 < b) (hbi : b < p.cutoff.rIn) (hν : p.exponent < 1)
    (s : System p b) (center : Maxwell.Space)
    (hball : ∀ x ∈ ball (0 : Maxwell.Space) b, x+center ∈ closedBall 0 1)
    (hE : ∀ i, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 b → totalCoordinate s i x =
      Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (x+center) i)
    (hq : ConicalIntrinsicCoefficient.coefficient s hb hbi hν ≠ 0)
    (r : ℝ) (hr : 0 < r) (hrb : r ≤ b) :
    ∃ i : Fin 3, ¬∃ M : ℝ, ∀ᵐ x : Maxwell.Space ∂volume.restrict (ball center r),
      ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z 1 1 u) i x‖ ≤ M := by
  let E : Field := fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (x+center)
  have hu := ConicalFixedInputTransfer.not_essentially_bounded p b hν s E hE _ hq
    (ConicalIntrinsicCoefficient.coefficient_spec s hb hbi hν) r hr hrb
  obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded E (ball 0 r) hu
  refine ⟨i,?_⟩
  rintro ⟨M,hM⟩
  apply hi
  refine ⟨M,?_⟩
  have hM' := (ae_restrict_iff' measurableSet_ball).mp hM
  have he := Packet06ComplexElectric.electric_ae_on_ball z 1 1 (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u 1 hc)
    (DynamicVolume.source_zero c u 1 hc) (StaticNewton.material_source_ae c u) i
  have hcoord := NewtonL2.physicalCoordinate_ae (Packet06LocalPencil.response c z 1 1 u) i
  have hglobal : (fun x => NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z 1 1 u) i x) =ᵐ[volume.restrict (closedBall 0 1)]
      fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i := by
    filter_upwards [ae_restrict_of_ae hcoord,he] with x hcoord' he'
    exact hcoord'.trans he'
  have hglobal' := (ae_restrict_iff' measurableSet_closedBall).mp hglobal
  have hshift := (measurePreserving_add_right (volume : Measure Maxwell.Space) center).quasiMeasurePreserving.ae (hM'.and hglobal')
  filter_upwards [ae_restrict_of_ae hshift,ae_restrict_mem measurableSet_ball] with x hx hxball
  have hxcenter : x+center ∈ ball center r := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_right,dist_zero_right,sub_zero] using hxball
  have hxb : x ∈ ball (0 : Maxwell.Space) b := ball_subset_ball hrb hxball
  have hm := hx.1 hxcenter
  rw [hx.2 (hball x hxb)] at hm
  exact hm

theorem rounded_peaks {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
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
    (r : ℝ) (hr : 0 < r) (hrb : r ≤ g.radius) (M : ℝ) :
    ∃ (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (coord : Fin N → Fin 3),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j) ∧
        ∀ i, 0 < (volume.restrict (ball (g.center i) r)) {x | M <
          ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 1 (v j)) (coord i) x‖}) := by
  obtain ⟨z,v,hz,hv,hresp,hgood⟩ := same_mode_rounding n hn g η hη z₀ u₀ hcert hN hre him Q hQ
  have hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 →
      (sharp n hn g η hη).value (VectorFourier.coordinateMap x) = 0 :=
    Packet06ContrastInsertion.support _ _ η hη 1 (ModalWeightedMode.coefficient_support n hn) (admissible g).2.2
  have hunbounded (i : Fin N) : ∃ k : Fin 3, ¬∃ B : ℝ, ∀ᵐ x : Maxwell.Space ∂volume.restrict (ball (g.center i) r),
      ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (sharp n hn g η hη) z₀ 1 1 u₀) k x‖ ≤ B := by
    apply sharp_coordinate_unbounded (sharp n hn g η hη) z₀ u₀ hsupp p g.radius g.radius_pos
      (by rw [hp.1]; exact g.radius_inner) hp.2 (s i) (g.center i) _ (hE i) (hq i) r hr hrb
    intro x hx
    exact ball_subset_closedBall ((Packet06ConcreteExcitation.local_geometry g i).1 x (ball_subset_closedBall hx))
  let coord : Fin N → Fin 3 := fun i => Classical.choose (hunbounded i)
  have hcoord (i : Fin N) := Classical.choose_spec (hunbounded i)
  have hpeak (i : Fin N) : ∀ᶠ j in atTop,
      0 < (volume.restrict (ball (g.center i) r)) {x | M <
        ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 1 (v j)) (coord i) x‖} := by
    have hlim := ((ConicalVolumePeaks.physicalCoordinateCLM (coord i)).continuous.tendsto _).comp (hresp 1 (by norm_num))
    exact L2PeakPreservation.eventually_positive_superlevel _ _ _ hlim (hcoord i) M
  refine ⟨z,v,coord,hz,hv,?_⟩
  filter_upwards [hgood,Filter.eventually_all.mpr hpeak] with j hj hp'
  exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hj.2.2.2.2.2.1,hj.2.2.2.2.2.2,hp'⟩
#print axioms OQ14.Packet06RoundedIntrinsicPeaks.sharp_coordinate_unbounded
#print axioms OQ14.Packet06RoundedIntrinsicPeaks.rounded_peaks
end OQ14.Packet06RoundedIntrinsicPeaks
