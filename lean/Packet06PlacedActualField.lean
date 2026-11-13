import Packet06PlacedMaterialField
import Packet06PlacedGreenSupport
import Packet06ComplexElectric
import Packet05ActualMaximum
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedActualField
open MeasureTheory Metric Set Maxwell Packet06PlacedKernel Packet06CyclicRotation
  Packet06PlacedMaterialField Packet06PlacedGreenSupport
open WeakCurl (previous)
open scoped Topology

/-- Exact component transport of the actual complex electric representatives
on the positive material region where both local response balls apply. -/
theorem electric_ae (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (U : ℝ) (hU : R/s+‖a‖ ≤ U) (i : Fin 3) :
    ∀ᵐ y : Space, y ∈ closedBall 0 U → unrotate (s • (y-a)) ∈ closedBall 0 T →
      c.value (VectorFourier.coordinateMap (unrotate (s • (y-a)))) ≠ 0 →
      Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) y i =
      ((Real.sqrt s*s : ℝ) : ℂ) * Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
        (unrotate (s • (y-a))) (previous i) := by
  obtain ⟨hpc,_,_,_⟩ := placed_normalized_kernel c R hR hc z u hu hN s hs a
  have hp := Packet06ComplexElectric.electric_ae_on_ball ((s : ℂ)*z) (R/s+‖a‖) U
    (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
    (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u))
    (DynamicVolume.source_integrable (placedCoefficient s a c) (placedUnknown s a u) (R/s+‖a‖) hpc)
    (DynamicVolume.source_zero (placedCoefficient s a c) (placedUnknown s a u) (R/s+‖a‖) hpc)
    (StaticNewton.material_source_ae (placedCoefficient s a c) (placedUnknown s a u)) i
  have hp' := (ae_restrict_iff' measurableSet_closedBall).mp hp
  have hb := Packet06ComplexElectric.electric_ae_on_ball z R T (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) (previous i)
  have hb' := (ae_restrict_iff' measurableSet_closedBall).mp hb
  let q : Space → Space := fun y => unrotate (s • (y-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hbr := hq.ae hb'
  have htransport := placed_response_material_ae c R T hR hRT hc z u hu hN s hs a U hU i
  filter_upwards [hp',hbr,htransport] with y hp hb ht hy hqT hpos
  have hh1 := hp hy
  have hh2 := hb hqT
  change Packet06LocalPencil.response (placedCoefficient s a c) ((s : ℂ)*z) (R/s+‖a‖) U
    (placedUnknown s a u) (VectorFourier.coordinateMap y) i = _ at hh1
  change Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap (q y)) (previous i) = _ at hh2
  rw [← hh1, ht hpos,hh2]

/-- Euclidean electric amplitude transforms with the positive reciprocal-mode
scale on the same physical positive-material region. -/
theorem amplitude_ae (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (U : ℝ) (hU : R/s+‖a‖ ≤ U) :
    ∀ᵐ y : Space, y ∈ closedBall 0 U → unrotate (s • (y-a)) ∈ closedBall 0 T →
      c.value (VectorFourier.coordinateMap (unrotate (s • (y-a)))) ≠ 0 →
      Packet05ActualMaximum.physicalAmplitude (fun i x => Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) x i) y =
      (Real.sqrt s*s) * Packet05ActualMaximum.physicalAmplitude (fun i x => Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i) (unrotate (s • (y-a))) := by
  have hall := ae_all_iff.mpr (fun i => electric_ae c R T hR hRT hc z u hu hN s hs a U hU i)
  filter_upwards [hall] with y hy hyU hyT hpos
  let β := Real.sqrt s*s
  have hβ : 0 ≤ β := mul_nonneg (Real.sqrt_nonneg _) hs.le
  simp only [Packet05ActualMaximum.physicalAmplitude]
  simp only [Fin.sum_univ_three]
  rw [hy 0 hyU hyT hpos, hy 1 hyU hyT hpos, hy 2 hyU hyT hpos]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg s), abs_of_pos hs, WeakCurl.previous,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  let e : Fin 3 → ℂ := fun i => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (unrotate (s • (y-a))) i
  change Real.sqrt ((β*‖e 2‖)^2+(β*‖e 0‖)^2+(β*‖e 1‖)^2) =
    β*Real.sqrt (‖e 0‖^2+‖e 1‖^2+‖e 2‖^2)
  rw [show (β*‖e 2‖)^2+(β*‖e 0‖)^2+(β*‖e 1‖)^2 =
    β^2*(‖e 0‖^2+‖e 1‖^2+‖e 2‖^2) by ring,
    Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,abs_of_nonneg hβ]
/-- On the placed image of the unit interior, the actual amplitudes agree
with the exact positive scale. -/
theorem amplitude_on_unit_image (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    ∀ᵐ x : Space, x ∈ ball 0 1 →
      Packet05ActualMaximum.physicalAmplitude (fun i y => Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) y i)
        (Packet06PhysicalPlacement.point s a x) =
      (Real.sqrt s*s) * Packet05ActualMaximum.physicalAmplitude (fun i y => Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) y i) x := by
  have he := (point_qmp s hs a).ae (amplitude_ae c 1 1 (by norm_num) le_rfl hc z u hu hN s hs a
    (1/s+‖a‖) le_rfl)
  filter_upwards [he] with x hx hball
  have hback : unrotate (s • (Packet06PhysicalPlacement.point s a x-a)) = x := by
    simp only [Packet06PhysicalPlacement.point,add_sub_cancel_left,smul_smul,
      mul_inv_cancel₀ hs.ne',one_smul,unrotate_rotate]
  have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using (ball_subset_closedBall hball : x ∈ closedBall 0 1)
  have hy : Packet06PhysicalPlacement.point s a x ∈ closedBall (0 : Space) (1/s+‖a‖) := by
    have hnorm : ‖Packet06PhysicalPlacement.point s a x‖ ≤ ‖a‖ + s⁻¹*‖x‖ := by
      simpa only [Packet06PhysicalPlacement.point,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs),rotate_norm] using norm_add_le a (s⁻¹ • rotate x)
    have hh : s⁻¹*‖x‖ ≤ s⁻¹ := by simpa using mul_le_mul_of_nonneg_left hx1 (inv_nonneg.mpr hs.le)
    simp only [mem_closedBall,dist_zero_right]
    rw [one_div]
    linarith
  have hh := hx hy (by rw [hback]; exact ball_subset_closedBall hball) (by rw [hback]; exact hpos x hball)
  simpa only [hback] using hh

/-- Every actual one-sided representative transports to the placed physical
amplitude almost everywhere on its phase, within the unit interior. -/
theorem branch_amplitude_on_unit_image (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (V : Set Space) (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) :
    ∀ᵐ x ∂volume.restrict V, x ∈ ball 0 1 →
      Packet05ActualMaximum.physicalAmplitude (fun i y => Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) y i)
        (Packet06PhysicalPlacement.point s a x) =
      (Real.sqrt s*s) * Packet05ActualMaximum.physicalAmplitude reps x := by
  have he := ae_restrict_of_ae (s := V) (amplitude_on_unit_image c hc hpos z u hu hN s hs a)
  have hr := ae_all_iff.mpr hreps
  filter_upwards [he,hr] with x hx hr hxball
  rw [hx hxball]
  congr 1
  simp only [Packet05ActualMaximum.physicalAmplitude]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [hr i])

/-- Target-coordinate form: the placed actual amplitude agrees almost
 everywhere with the pulled-back one-sided amplitude on the placed phase. -/
theorem branch_amplitude_target_ae (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (U : ℝ) (hU : 1/s+‖a‖ ≤ U)
    (V : Set Space) (hV : MeasurableSet V) (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) :
    ∀ᵐ y : Space, y ∈ closedBall 0 U → unrotate (s • (y-a)) ∈ V →
      unrotate (s • (y-a)) ∈ ball 0 1 →
      Packet05ActualMaximum.physicalAmplitude (fun i x => Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) x i) y =
      (Real.sqrt s*s) * Packet05ActualMaximum.physicalAmplitude reps (unrotate (s • (y-a))) := by
  let q : Space → Space := fun y => unrotate (s • (y-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have he := amplitude_ae c 1 1 (by norm_num) le_rfl hc z u hu hN s hs a U hU
  have hr : ∀ᵐ x : Space, x ∈ V → ∀ i, Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i = reps i x :=
    (ae_restrict_iff' hV).mp (ae_all_iff.mpr hreps)
  have hqr := hq.ae hr
  filter_upwards [he,hqr] with y he hr hy hVq hball
  rw [he hy (ball_subset_closedBall hball) (hpos _ hball)]
  congr 1
  simp only [Packet05ActualMaximum.physicalAmplitude]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [hr hVq i])

#print axioms OQ14.Packet06PlacedActualField.branch_amplitude_target_ae
#print axioms OQ14.Packet06PlacedActualField.branch_amplitude_on_unit_image
#print axioms OQ14.Packet06PlacedActualField.amplitude_on_unit_image
#print axioms OQ14.Packet06PlacedActualField.amplitude_ae
#print axioms OQ14.Packet06PlacedActualField.electric_ae
end OQ14.Packet06PlacedActualField
