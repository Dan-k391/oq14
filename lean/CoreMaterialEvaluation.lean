import BoundedMaterialKernel
import ConicalInteriorResponse

/-! Bounded evaluation of the literal material dyadic response inside a source-free core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OQ14.CoreMaterialEvaluation
open MeasureTheory Set Metric OQ14.Maxwell
open OQ14.DynamicConvolution (component component_apply)
attribute [local instance] Classical.propDecidable
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def annulus (R X : ℝ) : Set Space := closedBall 0 X \ ball 0 R

theorem annulus_compact (R X : ℝ) : IsCompact (annulus R X) :=
  (isCompact_closedBall (0 : Space) X).diff isOpen_ball

def supportData (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0) :
    BoundedMaterialKernel.SupportData c where
  radius := X
  carrier := annulus R X
  measurable := (annulus_compact R X).measurableSet
  finite := (annulus_compact R X).measure_lt_top.ne
  ballZero y hy := hc y (fun ha => hy ha.1)
  carrierZero := hc

theorem separated (R X : ℝ) (x : Space) (hx : ‖x‖<R) (y : Space)
    (hy : y∈annulus R X) : x-y≠0 := by
  intro he
  have hxy := sub_eq_zero.mp he
  have hn : R≤‖y‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hy.2
  exact (not_lt_of_ge hn) (hxy ▸ hx)

theorem kernel_continuousOn (R X : ℝ) (x : Space) (hx : ‖x‖<R) (i j : Fin 3) :
    ContinuousOn (fun y => DyadicKernel.dyadic 1 (x-y) i j) (annulus R X) := by
  intro y hy
  exact ((ExteriorContinuity.dyadic_continuousAt 1 i j (x-y) (separated R X x hx y hy)).comp
    (continuous_const.sub continuous_id).continuousAt).continuousWithinAt

def kernelBound (R X : ℝ) (x : Space) (hx : ‖x‖<R) (i j : Fin 3) : ℝ :=
  max 0 ((annulus_compact R X).exists_bound_of_continuousOn (kernel_continuousOn R X x hx i j)).choose

theorem kernelBound_nonnegative (R X : ℝ) (x : Space) (hx : ‖x‖<R) (i j : Fin 3) :
    0≤kernelBound R X x hx i j := le_max_left _ _

theorem kernel_bound (R X : ℝ) (x : Space) (hx : ‖x‖<R) (i j : Fin 3)
    (y : Space) (hy : y∈annulus R X) :
    ‖DyadicKernel.dyadic 1 (x-y) i j‖≤kernelBound R X x hx i j :=
  (((annulus_compact R X).exists_bound_of_continuousOn
    (kernel_continuousOn R X x hx i j)).choose_spec y hy).trans (le_max_right _ _)

def entry (c : Coefficient) (R X : ℝ) (x : Space) (i j : Fin 3) (u : VectorL2) : ℂ :=
  ∫ y in annulus R X, component j (StaticCoefficient.sqrtMultiplier c u) y*
    DyadicKernel.dyadic 1 (x-y) i j

theorem entry_integrable (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) (u : VectorL2) :
    IntegrableOn (fun y => component j (StaticCoefficient.sqrtMultiplier c u) y*
      DyadicKernel.dyadic 1 (x-y) i j) (annulus R X) := by
  exact (StaticNewton.material_source_integrable c u (closedBall 0 X)
    (isCompact_closedBall 0 X) (supportData c R X hc).ballZero j).integrableOn.mul_continuousOn
      (kernel_continuousOn R X x hx i j) (annulus_compact R X)

theorem entry_bound (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) (u : VectorL2) :
    ‖entry c R X x i j u‖≤
      (kernelBound R X x hx i j*Real.sqrt c.bound*Real.sqrt (volume.real (annulus R X)))*‖u‖ := by
  let v := component j (StaticCoefficient.sqrtMultiplier c u)
  have hv := StaticNewton.material_source_integrable c u (closedBall 0 X)
    (isCompact_closedBall 0 X) (supportData c R X hc).ballZero j
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ y in annulus R X, kernelBound R X x hx i j*‖v y‖ := by
      apply integral_mono_ae (entry_integrable c R X hc x hx i j u).norm
        (hv.norm.const_mul (kernelBound R X x hx i j)).integrableOn
      filter_upwards [ae_restrict_mem (annulus_compact R X).measurableSet] with y hy
      change ‖v y*DyadicKernel.dyadic 1 (x-y) i j‖≤_
      rw [norm_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (kernel_bound R X x hx i j y hy) (norm_nonneg _)
    _ = kernelBound R X x hx i j*(∫ y in annulus R X, ‖v y‖) := integral_const_mul _ _
    _ ≤ kernelBound R X x hx i j*(∫ y, ‖v y‖) := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hv.norm
        (Filter.Eventually.of_forall (fun y => norm_nonneg (v y)))) (kernelBound_nonnegative R X x hx i j)
    _ ≤ _ := by
      have hm := BoundedMaterialKernel.source_mass (supportData c R X hc) u j
      dsimp only [supportData] at hm
      exact (mul_le_mul_of_nonneg_left hm (kernelBound_nonnegative R X x hx i j)).trans_eq (by ring)

def entryLinear (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) : VectorL2 →ₗ[ℂ] ℂ where
  toFun := entry c R X x i j
  map_add' u v := by
    unfold entry
    rw [map_add,map_add,←integral_add (entry_integrable c R X hc x hx i j u)
      (entry_integrable c R X hc x hx i j v)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (component j (StaticCoefficient.sqrtMultiplier c u))
      (component j (StaticCoefficient.sqrtMultiplier c v)))] with y hy
    rw [hy]
    simp only [Pi.add_apply,add_mul]
  map_smul' z u := by
    unfold entry
    rw [map_smul,map_smul]
    simp only [RingHom.id_apply,smul_eq_mul]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul z (component j (StaticCoefficient.sqrtMultiplier c u)))] with y hy
    rw [hy]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

def entryMap (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) : VectorL2 →L[ℂ] ℂ :=
  (entryLinear c R X hc x hx i j).mkContinuous
    (kernelBound R X x hx i j*Real.sqrt c.bound*Real.sqrt (volume.real (annulus R X)))
      (entry_bound c R X hc x hx i j)

theorem entryMap_norm (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) :
    ‖entryMap c R X hc x hx i j‖≤
      kernelBound R X x hx i j*Real.sqrt c.bound*Real.sqrt (volume.real (annulus R X)) :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (kernelBound_nonnegative R X x hx i j) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (entry_bound c R X hc x hx i j)

theorem entry_actual (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) (u : VectorL2) :
    entryMap c R X hc x hx i j u=
      ∫ y, DynamicVolume.source c u j y*DyadicKernel.dyadic 1 (x-y) i j := by
  change (∫ y in annulus R X, _)=_
  rw [←integral_indicator (annulus_compact R X).measurableSet]
  apply integral_congr_ae
  filter_upwards [StaticNewton.material_source_ae c u j] with y hy
  by_cases hs : y∈annulus R X
  · rw [indicator_of_mem hs,component_apply,hy]
    rfl
  · rw [indicator_of_not_mem hs]
    simp only [DynamicVolume.source,hc y hs,Real.sqrt_zero,Complex.ofReal_zero,zero_mul]

theorem actual_integrand_integrable (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i j : Fin 3) (u : VectorL2) :
    Integrable (fun y => DynamicVolume.source c u j y*DyadicKernel.dyadic 1 (x-y) i j) := by
  have h := (integrable_indicator_iff (annulus_compact R X).measurableSet).mpr
    (entry_integrable c R X hc x hx i j u)
  apply h.congr
  filter_upwards [StaticNewton.material_source_ae c u j] with y hy
  by_cases hs : y∈annulus R X
  · rw [indicator_of_mem hs,component_apply,hy]
    rfl
  · rw [indicator_of_not_mem hs]
    simp only [DynamicVolume.source,hc y hs,Real.sqrt_zero,Complex.ofReal_zero,zero_mul]

def evaluation (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i : Fin 3) : VectorL2 →L[ℂ] ℂ :=
  ∑ j : Fin 3, entryMap c R X hc x hx i j

theorem evaluation_norm (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i : Fin 3) :
    ‖evaluation c R X hc x hx i‖≤∑ j : Fin 3,
      kernelBound R X x hx i j*Real.sqrt c.bound*Real.sqrt (volume.real (annulus R X)) := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => entryMap_norm c R X hc x hx i j))

theorem evaluation_actual (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i : Fin 3) (u : VectorL2) :
    evaluation c R X hc x hx i u=
      ∑ j : Fin 3, ∫ y, DynamicVolume.source c u j y*DyadicKernel.dyadic 1 (x-y) i j := by
  simp only [evaluation,ContinuousLinearMap.sum_apply,entry_actual]

theorem core_hasSum {α : Type*} (c : Coefficient) (R X : ℝ)
    (hc : ∀ y : Space, y∉annulus R X → c.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖<R) (i : Fin 3) (f : α → VectorL2) (u : VectorL2) (h : HasSum f u) :
    HasSum (fun a => ∑ j : Fin 3, ∫ y, DynamicVolume.source c (f a) j y*
      DyadicKernel.dyadic 1 (x-y) i j)
      (∑ j : Fin 3, ∫ y, DynamicVolume.source c u j y*DyadicKernel.dyadic 1 (x-y) i j) := by
  simpa only [evaluation_actual] using h.mapL (evaluation c R X hc x hx i)

end OQ14.CoreMaterialEvaluation


#print axioms OQ14.CoreMaterialEvaluation.annulus_compact
#print axioms OQ14.CoreMaterialEvaluation.separated
#print axioms OQ14.CoreMaterialEvaluation.kernel_continuousOn
#print axioms OQ14.CoreMaterialEvaluation.kernelBound_nonnegative
#print axioms OQ14.CoreMaterialEvaluation.kernel_bound
#print axioms OQ14.CoreMaterialEvaluation.entry_integrable
#print axioms OQ14.CoreMaterialEvaluation.entry_bound
#print axioms OQ14.CoreMaterialEvaluation.entryMap_norm
#print axioms OQ14.CoreMaterialEvaluation.entry_actual
#print axioms OQ14.CoreMaterialEvaluation.actual_integrand_integrable
#print axioms OQ14.CoreMaterialEvaluation.evaluation_norm
#print axioms OQ14.CoreMaterialEvaluation.evaluation_actual
#print axioms OQ14.CoreMaterialEvaluation.core_hasSum
