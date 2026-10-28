import ConicalSeparatedSource
import UnionFreeRunge

/-! A single fixed-contrast coefficient assembled from disjoint translated tips. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonMaterial
open MeasureTheory Set Metric OQ14.Maxwell
open scoped Topology
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def localValue (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (i : ι) (x : Space) : ℝ :=
  (ConicalSeparatedSource.material (p i) (a i)).value (VectorFourier.coordinateMap (x - center i))

omit [Fintype ι] [DecidableEq ι] in
theorem localValue_measurable (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (i : ι) :
    Measurable (localValue p a center i) :=
  (ConicalSeparatedSource.material (p i) (a i)).measurable.comp
    (VectorFourier.coordinateMap_preserving.measurable.comp (continuous_id.sub continuous_const).measurable)

omit [Fintype ι] [DecidableEq ι] in
theorem localValue_zero (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (i : ι)
    (x : Space) (hx : x ∉ closedBall (center i) (a i)) : localValue p a center i x = 0 := by
  apply ConicalSeparatedSource.material_compact
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx

omit [Fintype ι] [DecidableEq ι] in
theorem localValue_eq_inside (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (i : ι)
    (x : Space) (hx : x ∈ closedBall (center i) (a i)) :
    localValue p a center i x = (ConicalStaticVolume.coefficient (p i)).value
      (VectorFourier.coordinateMap (x - center i)) := by
  apply ConicalSeparatedSource.material_eq_inside
  simpa only [mem_closedBall, dist_eq_norm] using hx

def outer (p : ι → Data) (center : ι → Space) (i : ι) : Set Space :=
  closedBall (center i) (p i).cutoff.rOut

def materialBall (a : ι → ℝ) (center : ι → Space) (i : ι) : Set Space :=
  closedBall (center i) (a i)

variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (outer p center i) (outer p center j))

omit [Fintype ι] [DecidableEq ι] in
include ha in
theorem material_subset_outer (i : ι) : materialBall a center i ⊆ outer p center i :=
  closedBall_subset_closedBall (ha i)

omit [Fintype ι] [DecidableEq ι] in
include ha hsep in
theorem localValue_eq_zero_of_mem_outer (i j : ι) (hij : i ≠ j) (x : Space)
    (hx : x ∈ outer p center i) : localValue p a center j x = 0 := by
  apply localValue_zero
  intro hxj
  exact Set.disjoint_left.mp (hsep i j hij) hx (material_subset_outer p a center ha j hxj)

omit [DecidableEq ι] in
include ha hsep in
theorem sum_eq_local (i : ι) (x : Space) (hx : x ∈ outer p center i) :
    (∑ j, localValue p a center j x) = localValue p a center i x := by
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact localValue_eq_zero_of_mem_outer p a center ha hsep i j (Ne.symm hji) x hx
  · simp

omit [DecidableEq ι] in
include hB hcontrast ha hsep in
theorem sum_bound (x : Space) : (∑ i, localValue p a center i x) ≤ B := by
  by_cases hx : ∃ i, x ∈ outer p center i
  · obtain ⟨i, hi⟩ := hx
    rw [sum_eq_local p a center ha hsep i x hi]
    exact ((ConicalSeparatedSource.material (p i) (a i)).bounded _).trans (hcontrast i)
  · have hz : ∀ i, localValue p a center i x = 0 := by
      intro i
      apply localValue_zero
      intro hi
      exact hx ⟨i, material_subset_outer p a center ha i hi⟩
    simp [hz, hB]

def coefficient : StaticCoefficient.Coefficient where
  value ξ := ∑ i, localValue p a center i (VectorFourier.coordinateMap.symm ξ)
  bound := B
  measurable := (Finset.measurable_sum Finset.univ fun i _ => localValue_measurable p a center i).comp
    VectorFourier.coordinateMap.symm.measurable
  nonnegative ξ := Finset.sum_nonneg fun i _ => (ConicalSeparatedSource.material (p i) (a i)).nonnegative (VectorFourier.coordinateMap (VectorFourier.coordinateMap.symm ξ - center i))
  bounded ξ := sum_bound p a center B hB hcontrast ha hsep (VectorFourier.coordinateMap.symm ξ)

omit [DecidableEq ι] in
theorem coefficient_spatial (x : Space) :
    (coefficient p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) =
      ∑ i, localValue p a center i x := by simp [coefficient]

omit [DecidableEq ι] in
theorem coefficient_local (i : ι) (x : Space) (hx : x ∈ outer p center i) :
    (coefficient p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) =
      localValue p a center i x := by
  rw [coefficient_spatial, sum_eq_local p a center ha hsep i x hx]

omit [DecidableEq ι] in
theorem coefficient_support (R : ℝ) (hR : ∀ i, outer p center i ⊆ closedBall (0 : Space) R)
    (x : Space) (hx : x ∉ closedBall (0 : Space) R) :
    (coefficient p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) = 0 := by
  rw [coefficient_spatial]
  apply Finset.sum_eq_zero
  intro i hi
  apply localValue_zero
  intro hm
  exact hx (hR i (material_subset_outer p a center ha i hm))

def source (i : ι) (j : Fin 3) (x : Space) : ℂ :=
  ConicalSeparatedSource.physicalSource (p i) (a i) j (x - center i)

omit [Fintype ι] in
include ha hsep in
theorem source_zero_material (hai : ∀ i, a i < (p i).cutoff.rIn)
    (i j : ι) (t : Fin 3) (x : Space) (hx : x ∈ materialBall a center j) :
    source p a center i t x = 0 := by
  by_cases hij : i = j
  · subst j
    apply ConicalSeparatedSource.source_zero_material (p i) (a i) (hai i)
    simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx
  · apply ConicalSeparatedSource.source_zero_outer (p i) (a i)
      ((hai i).trans (p i).cutoff.rIn_lt_rOut).le
    have hxout : x ∉ outer p center i := by
      intro hi
      exact Set.disjoint_left.mp (hsep i j hij) hi (material_subset_outer p a center ha j hx)
    simpa only [outer, mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hxout


omit [Fintype ι] in
include ha hsep in
theorem source_zero_union (hai : ∀ i, a i < (p i).cutoff.rIn)
    (i : ι) (t : Fin 3) (x : Space)
    (hx : x ∈ UnionFreeRunge.balls center a) : source p a center i t x = 0 := by
  change x ∈ ⋃ j, closedBall (center j) (a j) at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact source_zero_material p a center ha hsep hai i j t x hj

omit [Fintype ι] [DecidableEq ι] in
theorem source_zero_global_outer (i : ι) (t : Fin 3) (R : ℝ)
    (hR : outer p center i ⊆ closedBall (0 : Space) R) (x : Space)
    (hx : x ∉ closedBall (0 : Space) R) (hai : a i ≤ (p i).cutoff.rOut) :
    source p a center i t x = 0 := by
  apply ConicalSeparatedSource.source_zero_outer (p i) (a i) hai
  have hh : x ∉ outer p center i := fun hi => hx (hR hi)
  simpa only [outer, mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hh

omit [DecidableEq ι] in
theorem coefficient_mul_electric (i : ι) (x : Space) (t : Fin 3) :
    ((coefficient p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) : ℂ) *
      ConicalComplexLocalization.complexify
        (ConicalCutoffGradient.cutElectric (p i).cutoff (p i).exponent (p i).eigenvalue (p i).threshold) (x - center i) t =
    (localValue p a center i x : ℂ) *
      ConicalComplexLocalization.complexify
        (ConicalCutoffGradient.cutElectric (p i).cutoff (p i).exponent (p i).eigenvalue (p i).threshold) (x - center i) t := by
  by_cases hx : x ∈ outer p center i
  · rw [coefficient_local p a center B hB hcontrast ha hsep i x hx]
  · have hz : x - center i ∉ closedBall (0 : Space) (p i).cutoff.rOut := by
      simpa only [outer, mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx
    simp [ConicalComplexLocalization.complexify,
      ConicalAnnularSource.cutElectric_zero_outer (p i).cutoff (p i).exponent (p i).eigenvalue (p i).threshold _ hz]

end OQ14.ConicalCommonMaterial

#print axioms OQ14.ConicalCommonMaterial.localValue_measurable
#print axioms OQ14.ConicalCommonMaterial.localValue_zero
#print axioms OQ14.ConicalCommonMaterial.localValue_eq_inside
#print axioms OQ14.ConicalCommonMaterial.material_subset_outer
#print axioms OQ14.ConicalCommonMaterial.localValue_eq_zero_of_mem_outer
#print axioms OQ14.ConicalCommonMaterial.sum_eq_local
#print axioms OQ14.ConicalCommonMaterial.sum_bound
#print axioms OQ14.ConicalCommonMaterial.coefficient_spatial
#print axioms OQ14.ConicalCommonMaterial.coefficient_local
#print axioms OQ14.ConicalCommonMaterial.coefficient_support
#print axioms OQ14.ConicalCommonMaterial.source_zero_material
#print axioms OQ14.ConicalCommonMaterial.source_zero_union
#print axioms OQ14.ConicalCommonMaterial.source_zero_global_outer
#print axioms OQ14.ConicalCommonMaterial.coefficient_mul_electric





