import Packet05FixedChartUniformField
import Packet05QuantitativeMaterialPhases
import Packet05FinitePhysicalCollar

/-! Actual uniform collar for the normalized rounded mode family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet05ActualUniformCollar
open MeasureTheory Set Metric Filter Maxwell Packet05FiniteFixedAtlas Packet05PhysicalChartBranches
  Packet05PhysicalGraphChart Packet05GraphSmooth Packet05ChartBasis Packet05GraphChartMap
  Packet05FinitePhysicalCollar Packet06ConcreteModalRounding
open scoped Topology

theorem local_actual_bound {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (x : Maxwell.Space) (hx : x ∈ physical chart)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (z0 : ℂ) (v0 : Packet06SectorOperator.Sector)
    (hzlim : Tendsto z atTop (𝓝 z0)) (hvlim : Tendsto v atTop (𝓝 v0))
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0) :
    ∃ O : Set Maxwell.Space, ∃ C : ℝ, IsOpen O ∧ x ∈ O ∧ 0 ≤ C ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂volume, y ∈ O → ∀ k,
        ‖Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k‖ ≤ C := by
  let q := physicalFlatMap chart.up chart.axis chart.graph
  obtain ⟨T,C,hT,hxT,hsub,hC,hfield⟩ :=
    Packet05FixedChartUniformField.fixed_chart_uniform_field n hn g η hη chart (q x) hx z v z0 v0 hzlim hvlim hz hmode
  let O := q ⁻¹' T
  have hq := physicalFlat_continuous chart.up chart.axis chart.graph (chart.regular.of_le (by decide))
  have hO : IsOpen O := hT.preimage hq
  have hplane : ∀ᵐ y : Maxwell.Space ∂volume, y 2 ≠ 0 := by
    rw [ae_iff]
    simpa using Packet05LocalDerivative.interface_plane_null
  have hqp := (physicalFlat_measure_preserving chart.up chart.axis chart.graph
    (chart.regular.of_le (show (1 : WithTop ℕ∞) ≤ 4 by decide)).continuous).quasiMeasurePreserving.ae hplane
  refine ⟨O,C,hO,hxT,hC,?_⟩
  filter_upwards [hfield] with j hj
  obtain ⟨lower,upper,hl,hu,hle,hue,hlb,hub⟩ := hj
  have hml : MeasurableSet (q ⁻¹' (T ∩ {y | y 2 < 0})) :=
    (hT.inter (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const)).measurableSet.preimage hq.measurable
  have hmu : MeasurableSet (q ⁻¹' (T ∩ {y | 0 < y 2})) :=
    (hT.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)).measurableSet.preimage hq.measurable
  have hael : ∀ k, ∀ᵐ y ∂volume, y ∈ q ⁻¹' (T ∩ {y | y 2 < 0}) →
      Packet06ComplexElectric.electric (z j) (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k = lower k y :=
    fun k => (ae_restrict_iff' hml).mp (hle k)
  have haeu : ∀ k, ∀ᵐ y ∂volume, y ∈ q ⁻¹' (T ∩ {y | 0 < y 2}) →
      Packet06ComplexElectric.electric (z j) (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k = upper k y :=
    fun k => (ae_restrict_iff' hmu).mp (hue k)
  filter_upwards [ae_all_iff.mpr hael, ae_all_iff.mpr haeu, hqp] with y hyl hyu hy0 hyO k
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · rw [hyl k ⟨hyO,hneg⟩]
    exact hlb k y ⟨hyO,hneg⟩
  · rw [hyu k ⟨hyO,hpos⟩]
    exact hub k y ⟨hyO,hpos⟩

theorem actual_uniform_collar {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (z0 : ℂ) (v0 : Packet06SectorOperator.Sector)
    (hzlim : Tendsto z atTop (𝓝 z0)) (hvlim : Tendsto v atTop (𝓝 v0))
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r < g.radius) :
    ∃ A : Set Maxwell.Space, ∃ B : ℝ, IsOpen A ∧ A ⊆ ball (g.center i) g.radius ∧
      sphere (g.center i) r ⊆ A ∧ 0 ≤ B ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂volume.restrict A,
        Packet05ActualMaximum.physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) y ≤ B := by
  obtain ⟨j0,hstable,hatlas⟩ := Packet05FixedCollarAtlas.actual_fixed_collar_atlas n hn g η hη
    (r/2) ((r+g.radius)/2) (by linarith) (by linarith)
  apply finite_physical_collar (g.center i) r g.radius hrR
  intro x hx
  have hxnorm : ‖x-g.center i‖=r := by simpa [mem_sphere,dist_eq_norm] using hx
  have hxann : x ∈ Packet05FixedCollarChart.annulus g i (r/2) ((r+g.radius)/2) := by
    change r/2 < ‖x-g.center i‖ ∧ ‖x-g.center i‖ < (r+g.radius)/2
    rw [hxnorm]
    constructor <;> linarith
  obtain ⟨up,axis,G,T,body,host,d,hG,hGc,hT,hxT,hhost,hd,hmap,hside,hmat⟩ := hatlas i x hxann
  let chart : Chart n hn g η hη := ⟨up,axis,G,T,body,host,d,hG,hGc,hT,hhost,hd,hmap,hside,hmat⟩
  exact local_actual_bound n hn g η hη chart x hxT z v z0 v0 hzlim hvlim hz hmode
end OQ14.Packet05ActualUniformCollar
#print axioms OQ14.Packet05ActualUniformCollar.local_actual_bound
#print axioms OQ14.Packet05ActualUniformCollar.actual_uniform_collar
