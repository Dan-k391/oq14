import BoundedMaterialKernel
import PhysicalReactionLimit

/-! Bounded continuous extensions of actual compact core kernels. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.CompactCoreKernel
open MeasureTheory Set Metric OQ14.Maxwell
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

def clampValue (b : ℝ) (p : Space × Space) : Space × Space :=
  (b/max b ‖p‖) • p

theorem clampValue_norm (b : ℝ) (hb : 0<b) (p : Space × Space) : ‖clampValue b p‖≤b := by
  have hd : 0<max b ‖p‖ := hb.trans_le (le_max_left _ _)
  rw [clampValue,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hb.le hd.le)]
  rw [div_mul_eq_mul_div,div_le_iff₀ hd]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le

theorem clampValue_eq (b : ℝ) (hb : 0<b) (p : Space × Space) (hp : ‖p‖≤b) : clampValue b p=p := by
  simp only [clampValue,max_eq_left hp,div_self hb.ne',one_smul]

def clamp (b : ℝ) (hb : 0<b) (p : Space × Space) : Region b :=
  ⟨clampValue b p,mem_closedBall_zero_iff.mpr (clampValue_norm b hb p)⟩

theorem clamp_continuous (b : ℝ) (hb : 0<b) : Continuous (clamp b hb) := by
  apply Continuous.subtype_mk
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun p => (hb.trans_le (le_max_left b ‖p‖)).ne')).smul continuous_id

def extension (b : ℝ) (hb : 0<b) (f : C(Region b,ℂ)) : BoundedMaterialKernel.Kernel where
  value x y := f (clamp b hb (x,y))
  continuous := f.continuous.comp (clamp_continuous b hb)
  bound := ‖f‖
  nonnegative := norm_nonneg f
  bounded _x _y := f.norm_coe_le_norm _

theorem extension_actual (b : ℝ) (hb : 0<b) (f : C(Region b,ℂ)) (p : Region b) :
    (extension b hb f).value p.val.1 p.val.2=f p := by
  change f (clamp b hb p.val)=f p
  congr 1
  exact Subtype.ext (clampValue_eq b hb p.val (region_norm b p))

theorem entry_sub (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (b : ℝ) (hb : 0<b) (f g : C(Region b,ℂ)) (u : VectorFourier.VectorL2) (j : Fin 3) :
    BoundedMaterialKernel.entry d (extension b hb (f-g)) u j=
      BoundedMaterialKernel.entry d (extension b hb f) u j-BoundedMaterialKernel.entry d (extension b hb g) u j := by
  apply Lp.ext
  filter_upwards [BoundedMaterialKernel.entry_ae d (extension b hb (f-g)) u j,
    BoundedMaterialKernel.entry_ae d (extension b hb f) u j,
    BoundedMaterialKernel.entry_ae d (extension b hb g) u j,
    Lp.coeFn_sub (BoundedMaterialKernel.entry d (extension b hb f) u j)
      (BoundedMaterialKernel.entry d (extension b hb g) u j)] with x hfg hf hg hs
  rw [hfg,hs]
  simp only [Pi.sub_apply]
  rw [hf,hg]
  have hif : Integrable (fun y => f (clamp b hb (x,y))*
      DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u) y) :=
    BoundedMaterialKernel.source_integrand_integrable d (extension b hb f) u j x
  have hig : Integrable (fun y => g (clamp b hb (x,y))*
      DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u) y) :=
    BoundedMaterialKernel.source_integrand_integrable d (extension b hb g) u j x
  simp only [BoundedMaterialKernel.value,BoundedMaterialKernel.sourceValue,
    extension,ContinuousMap.sub_apply,sub_mul]
  rw [integral_sub hif hig,mul_sub]

theorem operator_sub (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (b : ℝ) (hb : 0<b) (f g : Fin 3 → Fin 3 → C(Region b,ℂ)) :
    BoundedMaterialKernel.operator d (fun i j => extension b hb (f i j-g i j))=
      BoundedMaterialKernel.operator d (fun i j => extension b hb (f i j))-
        BoundedMaterialKernel.operator d (fun i j => extension b hb (g i j)) := by
  have he (i j : Fin 3) : BoundedMaterialKernel.entryOperator d (extension b hb (f i j-g i j)) j=
      BoundedMaterialKernel.entryOperator d (extension b hb (f i j)) j-
        BoundedMaterialKernel.entryOperator d (extension b hb (g i j)) j := by
    apply ContinuousLinearMap.ext
    intro u
    exact entry_sub c d b hb (f i j) (g i j) u j
  simp only [BoundedMaterialKernel.operator,he,ContinuousLinearMap.comp_sub,Finset.sum_sub_distrib]

theorem operator_difference_bound (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (b : ℝ) (hb : 0<b) (f g : Fin 3 → Fin 3 → C(Region b,ℂ)) :
    ‖BoundedMaterialKernel.operator d (fun i j => extension b hb (f i j))-
        BoundedMaterialKernel.operator d (fun i j => extension b hb (g i j))‖≤
      c.bound*volume.real d.carrier*∑ i : Fin 3,∑ j : Fin 3,‖f i j-g i j‖ := by
  rw [←operator_sub]
  exact BoundedMaterialKernel.operator_norm d _

end OQ14.CompactCoreKernel
#print axioms OQ14.CompactCoreKernel.clampValue_norm
#print axioms OQ14.CompactCoreKernel.clampValue_eq
#print axioms OQ14.CompactCoreKernel.clamp_continuous
#print axioms OQ14.CompactCoreKernel.extension_actual
#print axioms OQ14.CompactCoreKernel.entry_sub
#print axioms OQ14.CompactCoreKernel.operator_sub
#print axioms OQ14.CompactCoreKernel.operator_difference_bound
