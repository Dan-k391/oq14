import Packet07DrivenUniformFixedField
import Packet07DrivenUniformAtlas
import Packet05QuantitativeMaterialPhases
import Packet05FinitePhysicalCollar

/-! Actual uniform collar for the normalized rounded mode family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet07DrivenUniformCollar
open MeasureTheory Set Metric Filter Maxwell Packet07DrivenUniformFiniteAtlas Packet05PhysicalChartBranches
  Packet05PhysicalGraphChart Packet05GraphSmooth Packet05ChartBasis Packet05GraphChartMap
  Packet05FinitePhysicalCollar Packet07PlanarSetup
open scoped Topology

theorem local_actual_bound {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (chart : Chart g) (x : Maxwell.Space) (hx : x ∈ physical chart) :
    ∃ O : Set Maxwell.Space, ∃ C : ℝ, IsOpen O ∧ x ∈ O ∧ 0 ≤ C ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂volume, y ∈ O → ∀ k,
        ‖g.electric freq j input y k‖ ≤ C := by
  let q := physicalFlatMap chart.up chart.axis chart.graph
  obtain ⟨T,C,hT,hxT,hsub,hC,hfield⟩ :=
    Packet07DrivenUniformFixedField.fixed_chart_uniform_field g freq hfreq0 input hfreq chart (q x) hx
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
      g.electric freq j input y k = lower k y :=
    fun k => (ae_restrict_iff' hml).mp (hle k)
  have haeu : ∀ k, ∀ᵐ y ∂volume, y ∈ q ⁻¹' (T ∩ {y | 0 < y 2}) →
      g.electric freq j input y k = upper k y :=
    fun k => (ae_restrict_iff' hmu).mp (hue k)
  filter_upwards [ae_all_iff.mpr hael, ae_all_iff.mpr haeu, hqp] with y hyl hyu hy0 hyO k
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · rw [hyl k ⟨hyO,hneg⟩]
    exact hlb k y ⟨hyO,hneg⟩
  · rw [hyu k ⟨hyO,hpos⟩]
    exact hub k y ⟨hyO,hpos⟩

theorem actual_uniform_collar {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r < g.radius) :
    ∃ A : Set Maxwell.Space, ∃ B : ℝ, IsOpen A ∧ A ⊆ ball (g.centers i) g.radius ∧
      sphere (g.centers i) r ⊆ A ∧ 0 ≤ B ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂volume.restrict A,
        Packet05ActualMaximum.physicalAmplitude (fun k y => g.electric freq j input y k) y ≤ B := by
  obtain ⟨j0,hstable,hatlas⟩ := Packet07DrivenUniformAtlas.actual_fixed_collar_atlas g
    (r/2) ((r+g.radius)/2) (by linarith) (by linarith)
  apply finite_physical_collar (g.centers i) r g.radius hrR
  intro x hx
  have hxnorm : ‖x-g.centers i‖=r := by simpa [mem_sphere,dist_eq_norm] using hx
  have hxann : x ∈ Packet07DrivenUniformCollarChart.annulus g i (r/2) ((r+g.radius)/2) := by
    change r/2 < ‖x-g.centers i‖ ∧ ‖x-g.centers i‖ < (r+g.radius)/2
    rw [hxnorm]
    constructor <;> linarith
  obtain ⟨up,axis,G,T,body,host,d,hG,hGc,hT,hxT,hhost,hd,hmap,hside,hmat⟩ := hatlas i x hxann
  let chart : Chart g := ⟨up,axis,G,T,body,host,d,hG,hGc,hT,hhost,hd,hmap,hside,hmat⟩
  exact local_actual_bound g freq hfreq0 input hfreq chart x hxT
end OQ14.Packet07DrivenUniformCollar
#print axioms OQ14.Packet07DrivenUniformCollar.local_actual_bound
#print axioms OQ14.Packet07DrivenUniformCollar.actual_uniform_collar
