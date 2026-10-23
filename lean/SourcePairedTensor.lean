import SourceTensorJets
import SourcePairedGeometry
import PairedVectorKernelLimit

/-! Actual material-inverse tensors of physical finite shells have the full compact joint-jet limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourcePairedTensor
open Filter Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.HarmonicSpatialMajorant
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

def material (q : ℝ) (hq : 1≤q) (n r : ℕ) : StaticCoefficient.Coefficient :=
  SourceMaterialCoefficient.coefficient (physicalData q (zero_lt_one.trans_le hq) n r) (q^2)
    (by nlinarith) (physical_material_bounds q (zero_lt_one.trans_le hq) hq n r)

def kernel (q : ℝ) (hq : 1≤q) (n r : ℕ) (i j : Fin 3) : Space × Space → ℂ :=
  SourceTensorSeries.kernel (material q hq n r) (physicalData q (zero_lt_one.trans_le hq) n r) i j

theorem eventually_actual_jets (q : ℝ) (hq : 1≤q) (n m : ℕ) (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    ∀ᶠ r : ℕ in atTop,∀ p : Region b,
      iteratedFDeriv ℝ m (kernel q hq n r i j) p.val=
        PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n m b i j r p := by
  let B := max 1 (max (degreeScale 2 (b+1)) (degreeScale (m+2) (b+1)))
  let T := max 2 (2*(B*AngularExteriorBounds.base))
  have hB : 1≤B := le_max_left _ _
  have hB0 : 0≤B := zero_le_one.trans hB
  have hfB : degreeScale 2 (b+1)≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hdB : degreeScale (m+2) (b+1)≤B := (le_max_right _ _).trans (le_max_right _ _)
  have hq2 : 1≤q^2 := by nlinarith
  filter_upwards [PairedVectorKernelLimit.eventually_actual_apply q hq n m b hb i j,
    radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*B)),
    radius_tendsto.eventually (eventually_ge_atTop (width (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n))),
    radius_tendsto.eventually (eventually_gt_atTop T),
    radius_tendsto.eventually (eventually_gt_atTop (b+1))] with r ha hR he hwidth hT hbR
  intro p
  let d := physicalData q (zero_lt_one.trans_le hq) n r
  have hmat := physical_material_bounds q (zero_lt_one.trans_le hq) hq n r
  have hdisp := physical_dispersion q (zero_lt_one.trans_le hq) n r
  have hm (x : Space) : ((material q hq n r).value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1 :=
    SourceMaterialCoefficient.value_complex d (q^2) hq2 hmat x
  have hu : IsUnit (DynamicVolume.volumeBlock (material q hq n r) 1 d.X) :=
    SourceMaterialPartition.volumeBlock_isUnit d (q^2) hq2 hmat 1 (by norm_num)
  have hX : d.X≤2*d.R := by change radius r+width _≤2*radius r; linarith
  have hp : ‖p.val‖<b+1 := by have h := region_norm b p; linarith
  have hk := SourceTensorJets.kernel_jet_eq_series (material q hq n r) d hm hdisp hu
    (b+1) B T (by linarith) hB0 hfB (le_max_left _ _) (le_max_right _ _) hT hbR p.val hp i j m
  have hs := SourceTensorJets.series_derivative d q (q^2) B hq hq2 hR hB he hX hmat hdisp
    (fun g hg => (physical_parameters q (zero_lt_one.trans_le hq) hq n r g hg).2.2.2)
    m m le_rfl (b+1) (by linarith) hdB p.val hp i j
  have hte : VectorReactionSeries.series false i j (d.gs.map SourceDielectricModes.teLayer) d.R d.X d.hR=
      VectorReactionSeries.series false i j
        (layers (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) (radius r) (radius_pos r))
        (radius r) (radius r+width (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)) (radius_pos r) := by
    dsimp only [d]
    rw [physical_te_layers,physical_te_outer]
    rfl
  rw [ha p]
  simpa only [hte] using hk.trans hs

theorem uniform_actual_jet_limit (q : ℝ) (hq : 1≤q) (n m : ℕ) (b : ℝ) (hb : 0≤b)
    (i j : Fin 3) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop,∀ p : Region b,
      ‖iteratedFDeriv ℝ m (kernel q hq n r i j) p.val-
        iteratedFDeriv ℝ m (VectorLimitIdentification.kernel q n i j) p.val‖<ε := by
  have h : ∀ᶠ r : ℕ in atTop,
      PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n m b i j r ∈
        Metric.ball (PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n m b i j) ε :=
    (PairedVectorKernelLimit.uniform_kernel_jet_limit q hq n m b hb i j).eventually
      (Metric.ball_mem_nhds (PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n m b i j) hε)
  filter_upwards [h,eventually_actual_jets q hq n m b hb i j] with r hr he
  intro p
  rw [he p,←PairedVectorKernelLimit.kernelJetMap_apply q hq n m b hb i j p]
  have hn := (PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n m b i j r-
    PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n m b i j).norm_coe_le_norm p
  have hd := _root_.dist_eq_norm
    (PairedVectorKernelLimit.actualJetMap q (zero_lt_one.trans_le hq) n m b i j r)
    (PairedVectorKernelLimit.kernelJetMap q (zero_lt_one.trans_le hq) n m b i j)
  change dist _ _<ε at hr
  rw [hd] at hr
  exact hn.trans_lt hr

end OQ14.SourcePairedTensor
#print axioms OQ14.SourcePairedTensor.eventually_actual_jets
#print axioms OQ14.SourcePairedTensor.uniform_actual_jet_limit
