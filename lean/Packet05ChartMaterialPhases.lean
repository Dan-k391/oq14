import Packet05BoundaryPhaseChart

/-! The actual chart-side law identifies the continuous branches with the
literal material phases; only the null interface is discarded a.e. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ChartMaterialPhases
open MeasureTheory Set Maxwell Packet05ChartBasis Packet05ChartLinearEquiv
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches
  Packet05GraphSmooth Packet05LocalDerivative

theorem actual_material_phases (body : Set Space) (up : Bool) (axis : Fin 3)
    (g : ConicalSmoothJunction.Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : IsOpen T) (x : Space) (hx : physicalFlatMap up axis g x ∈ T)
    (hside : ∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight g) y) ∈ body ↔ 0 < y 2)
    (E : Field) (lower upper : Fin 3 → Space → ℂ)
    (hl : ∀ j, Continuous (lower j)) (hu : ∀ j, Continuous (upper j))
    (hle : ∀ j, (fun y => E y j) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}))] lower j)
    (hue : ∀ j, (fun y => E y j) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}))] upper j) :
    ∃ V : Set Space, IsOpen V ∧ x ∈ V ∧
      (∀ j, Continuous (upper j)) ∧ (∀ j, Continuous (lower j)) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ body)] upper j) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ bodyᶜ)] lower j) := by
  let q := physicalFlatMap up axis g
  let V := q ⁻¹' T
  have hq := physicalFlat_continuous up axis g hg
  have hV : IsOpen V := hT.preimage hq
  have hbody (y : Space) (hy : y ∈ V) : y ∈ body ↔ 0 < q y 2 := by
    have hh := hside (q y) hy
    have hback : inverseOriented up axis (graphMap (liftedHeight g) (q y))=y := by
      change inverseOriented up axis (graphMap (liftedHeight g)
        (inverseGraphMap (liftedHeight g) (orientedLinear up axis y)))=y
      rw [graph_map_right_inverse _ (liftedHeight_normal_invariant g)]
      exact inverse_oriented_left up axis y
    rwa [hback] at hh
  have hpos : V ∩ body=q ⁻¹' (T ∩ {y | 0 < y 2}) := by
    ext y
    constructor
    · rintro ⟨hy,hb⟩
      exact ⟨hy,(hbody y hy).mp hb⟩
    · rintro ⟨hy,hp⟩
      exact ⟨hy,(hbody y hy).mpr hp⟩
  have hneg : V ∩ bodyᶜ=q ⁻¹' (T ∩ {y | y 2 ≤ 0}) := by
    ext y
    constructor
    · rintro ⟨hy,hb⟩
      exact ⟨hy,le_of_not_gt (fun hp => hb ((hbody y hy).mpr hp))⟩
    · rintro ⟨hy,hn⟩
      exact ⟨hy,fun hb => (not_lt_of_ge hn) ((hbody y hy).mp hb)⟩
  have hmneg : MeasurableSet (V ∩ bodyᶜ) := by
    rw [hneg]
    exact (hT.measurableSet.inter
      (isClosed_le (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const).measurableSet).preimage hq.measurable
  have hmlo : MeasurableSet (q ⁻¹' (T ∩ {y | y 2 < 0})) :=
    (hT.inter (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const)).measurableSet.preimage hq.measurable
  have hplane : ∀ᵐ y : Space ∂volume, y 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  have hqplane := (physicalFlat_measure_preserving up axis g hg.continuous).quasiMeasurePreserving.ae hplane
  refine ⟨V,hV,hx,hu,hl,?_,?_⟩
  · intro j
    rw [hpos]
    exact hue j
  · intro j
    have hh := (ae_restrict_iff' hmlo).mp (hle j)
    apply (ae_restrict_iff' hmneg).mpr
    filter_upwards [hh,hqplane] with y hy hn hyV
    have hnonpos : q y 2 ≤ 0 := le_of_not_gt (fun h => hyV.2 ((hbody y hyV.1).mpr h))
    exact hy ⟨hyV.1,lt_of_le_of_ne hnonpos hn⟩

end OQ14.Packet05ChartMaterialPhases
#print axioms OQ14.Packet05ChartMaterialPhases.actual_material_phases
