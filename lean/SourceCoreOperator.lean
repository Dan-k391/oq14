import SourcePairedCore

/-! Material operators depend only on kernel values over the support; the clamped paired-core
operators are therefore the actual shell-tensor operators on the inclusion support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.SourceCoreOperator
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.DynamicConvolution
open PhysicalReactionLimit (Region)
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Kernel := BoundedMaterialKernel.Kernel

variable {c : StaticCoefficient.Coefficient}

theorem sourceValue_congr (d : BoundedMaterialKernel.SupportData c) (A B : Kernel)
    (hAB : ∀ x ∈ d.carrier,∀ y ∈ d.carrier,A.value x y=B.value x y) (u : VectorL2) (j : Fin 3)
    (x : Maxwell.Space) (hx : x ∈ d.carrier) :
    BoundedMaterialKernel.sourceValue d A u j x=BoundedMaterialKernel.sourceValue d B u j x := by
  unfold BoundedMaterialKernel.sourceValue
  apply integral_congr_ae
  filter_upwards [StaticNewton.material_source_ae c u j] with y hy
  by_cases hyc : y ∈ d.carrier
  · rw [hAB x hx y hyc]
  · rw [component_apply,hy,d.carrierZero y hyc]
    simp

theorem value_congr (d : BoundedMaterialKernel.SupportData c) (A B : Kernel)
    (hAB : ∀ x ∈ d.carrier,∀ y ∈ d.carrier,A.value x y=B.value x y) (u : VectorL2) (j : Fin 3) :
    BoundedMaterialKernel.value d A u j=BoundedMaterialKernel.value d B u j := by
  funext x
  by_cases hx : x ∈ d.carrier
  · unfold BoundedMaterialKernel.value
    rw [sourceValue_congr d A B hAB u j x hx]
  · simp [BoundedMaterialKernel.value,d.carrierZero x hx]

theorem entry_congr (d : BoundedMaterialKernel.SupportData c) (A B : Kernel)
    (hAB : ∀ x ∈ d.carrier,∀ y ∈ d.carrier,A.value x y=B.value x y) (u : VectorL2) (j : Fin 3) :
    BoundedMaterialKernel.entry d A u j=BoundedMaterialKernel.entry d B u j := by
  apply Lp.ext
  filter_upwards [BoundedMaterialKernel.entry_ae d A u j,BoundedMaterialKernel.entry_ae d B u j] with x ha hb
  rw [ha,hb,value_congr d A B hAB u j]

theorem operator_congr (d : BoundedMaterialKernel.SupportData c) (A B : Fin 3 → Fin 3 → Kernel)
    (hAB : ∀ i j,∀ x ∈ d.carrier,∀ y ∈ d.carrier,(A i j).value x y=(B i j).value x y) :
    BoundedMaterialKernel.operator d A=BoundedMaterialKernel.operator d B := by
  have he (i j : Fin 3) : BoundedMaterialKernel.entryOperator d (A i j) j=
      BoundedMaterialKernel.entryOperator d (B i j) j := by
    apply ContinuousLinearMap.ext
    intro u
    exact entry_congr d (A i j) (B i j) (hAB i j) u j
  simp only [BoundedMaterialKernel.operator,he]

theorem pair_mem_region (b : ℝ) (x y : Maxwell.Space) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ b) :
    (x,y) ∈ closedBall (0 : Maxwell.Space × Maxwell.Space) b := by
  rw [mem_closedBall_zero_iff,Prod.norm_def]
  exact max_le hx hy

section Core
variable (c) (d : BoundedMaterialKernel.SupportData c) (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b)
  (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
include hcar

theorem eventually_clamped_entries_actual (i j : Fin 3) :
    ∀ᶠ r : ℕ in atTop,∀ x ∈ d.carrier,∀ y ∈ d.carrier,
      (CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)).value x y=
        SourcePairedTensor.kernel q hq n r i j (x,y) := by
  filter_upwards [SourcePairedCore.eventually_entries_actual q hq n b hb i j] with r hr
  intro x hx y hy
  exact hr ⟨(x,y),pair_mem_region b x y (hcar x hx) (hcar y hy)⟩

theorem eventually_operator_eq (K : ℕ → Fin 3 → Fin 3 → Kernel)
    (hK : ∀ᶠ r : ℕ in atTop,∀ i j,∀ x ∈ d.carrier,∀ y ∈ d.carrier,
      (K r i j).value x y=SourcePairedTensor.kernel q hq n r i j (x,y)) :
    ∀ᶠ r : ℕ in atTop,SourcePairedCore.operator c d q hq n b hb r=BoundedMaterialKernel.operator d (K r) := by
  have hall : ∀ᶠ r : ℕ in atTop,∀ i j : Fin 3,∀ x ∈ d.carrier,∀ y ∈ d.carrier,
      (CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)).value x y=
        SourcePairedTensor.kernel q hq n r i j (x,y) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
      (fun j => eventually_clamped_entries_actual c d q hq n b hb hcar i j))
  filter_upwards [hall,hK] with r hr hKr
  apply operator_congr
  intro i j x hx y hy
  rw [hr i j x hx y hy,hKr i j x hx y hy]

theorem eventually_component_actual (u : VectorL2) (i : Fin 3) :
    ∀ᶠ r : ℕ in atTop,component i (SourcePairedCore.operator c d q hq n b hb r u) =ᵐ[volume]
      fun x => ∑ j : Fin 3,(Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
        ∫ y,SourcePairedTensor.kernel q hq n r i j (x,y)*DynamicVolume.source c u j y := by
  have hall : ∀ᶠ r : ℕ in atTop,∀ j : Fin 3,∀ x ∈ d.carrier,∀ y ∈ d.carrier,
      (CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)).value x y=
        SourcePairedTensor.kernel q hq n r i j (x,y) :=
    Filter.eventually_all.mpr (fun j => eventually_clamped_entries_actual c d q hq n b hb hcar i j)
  filter_upwards [hall] with r hr
  filter_upwards [BoundedMaterialKernel.component_operator_ae d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)) u i] with x hx
  change component i (BoundedMaterialKernel.operator d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)) u) x=_
  rw [hx]
  by_cases hxc : x ∈ d.carrier
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply integral_congr_ae
    filter_upwards [StaticNewton.material_source_ae c u j] with y hy
    by_cases hyc : y ∈ d.carrier
    · rw [hr j x hxc y hyc,component_apply,hy]
      rfl
    · rw [component_apply,hy,DynamicVolume.source,d.carrierZero y hyc]
      simp
  · simp [d.carrierZero x hxc]

end Core
end OQ14.SourceCoreOperator
#print axioms OQ14.SourceCoreOperator.sourceValue_congr
#print axioms OQ14.SourceCoreOperator.value_congr
#print axioms OQ14.SourceCoreOperator.entry_congr
#print axioms OQ14.SourceCoreOperator.operator_congr
#print axioms OQ14.SourceCoreOperator.pair_mem_region
#print axioms OQ14.SourceCoreOperator.eventually_clamped_entries_actual
#print axioms OQ14.SourceCoreOperator.eventually_operator_eq
#print axioms OQ14.SourceCoreOperator.eventually_component_actual
