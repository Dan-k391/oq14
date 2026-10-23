import SourcePairedTensor
import CompactCoreKernel

/-! Actual paired-shell core kernels converge in the material operator norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourcePairedCore
open MeasureTheory Filter Set Metric OQ14.Maxwell
open PhysicalReactionLimit (Region Jet)
open scoped Topology

def valueProjection (b : ℝ) : C(Region b,Jet 0) →L[ℝ] C(Region b,ℂ) :=
  (continuousMultilinearCurryFin0 ℝ (Space × Space) ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuousCompact (Region b)

def actualMap (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (i j : Fin 3) (r : ℕ) : C(Region b,ℂ) :=
  valueProjection b (PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n 0 b i j r)

def limitMap (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (i j : Fin 3) : C(Region b,ℂ) :=
  valueProjection b (PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n 0 b i j)

theorem limitMap_apply (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0≤b)
    (i j : Fin 3) (p : Region b) : limitMap q hq n b i j p=VectorLimitIdentification.kernel q n i j p.val := by
  change (PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n 0 b i j p) 0=_
  rw [PairedVectorKernelLimit.kernelJetMap_apply q hq n 0 b hb i j p,iteratedFDeriv_zero_apply]

theorem actualMap_limit (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    Tendsto (actualMap q hq n b i j) atTop (𝓝 (limitMap q hq n b i j)) :=
  (valueProjection b).continuous.continuousAt.tendsto.comp
    (PairedVectorKernelLimit.uniform_kernel_jet_limit q hq n 0 b hb i j)

theorem eventually_actualMap (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    ∀ᶠ r : ℕ in atTop,∀ p : Region b,actualMap q hq n b i j r p=SourcePairedTensor.kernel q hq n r i j p.val := by
  filter_upwards [SourcePairedTensor.eventually_actual_jets q hq n 0 b hb i j] with r hr
  intro p
  change (PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n 0 b i j r p) 0=_
  rw [←hr p,iteratedFDeriv_zero_apply]

def operator (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) (r : ℕ) :
    VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  BoundedMaterialKernel.operator d (fun i j => CompactCoreKernel.extension b hb (actualMap q hq n b i j r))

def limitingOperator (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) :
    VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  BoundedMaterialKernel.operator d (fun i j => CompactCoreKernel.extension b hb (limitMap q hq n b i j))

theorem operator_limit (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) :
    Tendsto (operator c d q hq n b hb) atTop (𝓝 (limitingOperator c d q hq n b hb)) := by
  have hs : Tendsto (fun r : ℕ => ∑ i : Fin 3,∑ j : Fin 3,
      ‖actualMap q hq n b i j r-limitMap q hq n b i j‖) atTop (𝓝 0) := by
    have he (i j : Fin 3) := tendsto_iff_norm_sub_tendsto_zero.mp (actualMap_limit q hq n b hb.le i j)
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ
      (fun i _ => tendsto_finset_sum Finset.univ (fun j _ => he i j))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun r => norm_nonneg _))
    (Filter.Eventually.of_forall (fun r => CompactCoreKernel.operator_difference_bound c d b hb
      (fun i j => actualMap q hq n b i j r) (fun i j => limitMap q hq n b i j)))
  simpa only [mul_zero] using hs.const_mul (c.bound*volume.real d.carrier)

theorem eventually_entries_actual (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) (i j : Fin 3) :
    ∀ᶠ r : ℕ in atTop,∀ p : Region b,
      (CompactCoreKernel.extension b hb (actualMap q hq n b i j r)).value p.val.1 p.val.2=
        SourcePairedTensor.kernel q hq n r i j p.val := by
  filter_upwards [eventually_actualMap q hq n b hb.le i j] with r hr
  intro p
  rw [CompactCoreKernel.extension_actual,hr p]

end OQ14.SourcePairedCore
#print axioms OQ14.SourcePairedCore.limitMap_apply
#print axioms OQ14.SourcePairedCore.actualMap_limit
#print axioms OQ14.SourcePairedCore.eventually_actualMap
#print axioms OQ14.SourcePairedCore.operator_limit
#print axioms OQ14.SourcePairedCore.eventually_entries_actual
