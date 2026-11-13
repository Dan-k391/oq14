import Packet06PlacedActualField
import Packet06PlacedPhaseField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedActualPhase
open MeasureTheory Metric Set Maxwell Packet06PlacedKernel Packet06CyclicRotation
  Packet06PlacedMaterialField Packet06PlacedPhaseField Packet06PlacementHomeomorph
open scoped Topology

/-- The transported one-sided components agree with the actual placed
complex electric field a.e. on the image of any measurable base phase
inside the positive-material unit ball. -/
theorem component_target_ae (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (V : Set Space) (hV : MeasurableSet V)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) (i : Fin 3) :
    ∀ᵐ y : Space, (placement s hs a).symm y ∈ V → (placement s hs a).symm y ∈ ball 0 1 →
      Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) y i =
      transport s hs a reps i y := by
  let q : Space → Space := fun y => unrotate (s • (y-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hr := (ae_restrict_iff' hV).mp (hreps (WeakCurl.previous i))
  have hqr := hq.ae hr
  have he := Packet06PlacedActualField.electric_ae c 1 1 (by norm_num) le_rfl hc z u hu hN s hs a
    (1/s+‖a‖) le_rfl i
  filter_upwards [he,hqr] with y he hr hyV hyB
  change q y ∈ V at hyV
  change q y ∈ ball 0 1 at hyB
  have hx1 : ‖q y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using
    (ball_subset_closedBall hyB : q y ∈ closedBall 0 1)
  have hy : y ∈ closedBall (0 : Space) (1/s+‖a‖) := by
    have hback : Packet06PhysicalPlacement.point s a (q y)=y :=
      (placement s hs a).apply_symm_apply y
    have hnorm : ‖Packet06PhysicalPlacement.point s a (q y)‖ ≤ ‖a‖ + s⁻¹*‖q y‖ := by
      simpa only [Packet06PhysicalPlacement.point,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs),rotate_norm] using norm_add_le a (s⁻¹ • rotate (q y))
    have hh : s⁻¹*‖q y‖ ≤ s⁻¹ := by simpa using mul_le_mul_of_nonneg_left hx1 (inv_nonneg.mpr hs.le)
    simp only [mem_closedBall,dist_zero_right]
    rw [←hback,one_div]
    linarith
  have hh := he hy (ball_subset_closedBall hyB) (hpos _ hyB)
  rw [hh,hr hyV]
  rfl

/-- Restricted-measure form on the literal image of the base phase. -/
theorem component_image_ae (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a : Space) (V : Set Space) (hV : MeasurableSet V)
    (hVball : V ⊆ ball 0 1) (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) (i : Fin 3) :
    (fun y => Packet06ComplexElectric.electric ((s : ℂ)*z)
      (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
      (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) y i) =ᵐ[
      volume.restrict (placement s hs a '' V)] transport s hs a reps i := by
  have hset : MeasurableSet (placement s hs a '' V) := by
    change MeasurableSet ((placement s hs a).toEquiv '' V)
    rw [(placement s hs a).toEquiv.image_eq_preimage]
    exact hV.preimage (placement s hs a).symm.continuous.measurable
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [component_target_ae c hc hpos z u hu hN s hs a V hV reps hreps i] with y hy hymem
  obtain ⟨x,hx,rfl⟩ := hymem
  apply hy
  · simpa using hx
  · simpa using hVball hx

#print axioms OQ14.Packet06PlacedActualPhase.component_image_ae
#print axioms OQ14.Packet06PlacedActualPhase.component_target_ae
end OQ14.Packet06PlacedActualPhase
