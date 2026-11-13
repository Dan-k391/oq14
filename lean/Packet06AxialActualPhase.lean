import Packet06AxialPhaseField

/-! Actual one-sided electric component representatives under axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialActualPhase
open MeasureTheory Metric Set Maxwell ModalAxialRotation Packet06AxialMaterialTransport
  Packet06AxialActualField Packet06AxialPhaseField

theorem component_image_general_ae (θ : ℝ) (c : StaticCoefficient.Coefficient) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (V : Set Space) (hV : MeasurableSet V) (hVball : V ⊆ closedBall 0 T)
    (hpos : ∀ x ∈ V, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) (i : Fin 3) :
    (fun y => Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y i) =ᵐ[
      volume.restrict ((rotation θ) '' V)] transport θ reps i := by
  have hset : MeasurableSet ((rotation θ) '' V) := by
    change MeasurableSet ((rotation θ).toEquiv '' V)
    rw [(rotation θ).toEquiv.image_eq_preimage]
    exact hV.preimage (rotation θ).symm.continuous.measurable
  have hrep := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
    (ae_all_iff.mpr (fun j => (ae_restrict_iff' hV).mp (hreps j)))
  have he := rotated_electric_material_ae θ c z R T hR hRT hc u hu hN i
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hrep,he] with y hr he' hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hback : rotation (-θ) (rotation θ x) = x := spatial_inverse θ x
  have hyball : rotation θ x ∈ closedBall (0 : Space) T := by
    simpa [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using (hVball hx)
  have hχ : c.value (VectorFourier.coordinateMap (rotation (-θ) (rotation θ x))) ≠ 0 := by
    rw [hback]; exact hpos x hx
  rw [he' hyball hχ]
  unfold transport
  apply Finset.sum_congr rfl
  intro j _
  rw [hr j (by simpa only [hback] using hx)]

theorem component_image_ae (θ : ℝ) (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (V : Set Space) (hV : MeasurableSet V) (hVball : V ⊆ ball 0 1)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) (i : Fin 3) :
    (fun y => Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y i) =ᵐ[
      volume.restrict ((rotation θ) '' V)] transport θ reps i := by
  have hset : MeasurableSet ((rotation θ) '' V) := by
    change MeasurableSet ((rotation θ).toEquiv '' V)
    rw [(rotation θ).toEquiv.image_eq_preimage]
    exact hV.preimage (rotation θ).symm.continuous.measurable
  have hrep := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
    (ae_all_iff.mpr (fun j => (ae_restrict_iff' hV).mp (hreps j)))
  have he := rotated_electric_material_ae θ c z 1 1 (by norm_num) le_rfl hc u hu hN i
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hrep,he] with y hr he' hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hback : rotation (-θ) (rotation θ x) = x := spatial_inverse θ x
  have hyball : rotation θ x ∈ closedBall (0 : Space) 1 := by
    simpa [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using (ball_subset_closedBall (hVball hx))
  have hχ : c.value (VectorFourier.coordinateMap (rotation (-θ) (rotation θ x))) ≠ 0 := by
    rw [hback]; exact hpos x (hVball hx)
  rw [he' hyball hχ]
  unfold transport
  apply Finset.sum_congr rfl
  intro j _
  rw [hr j (by simpa only [hback] using hx)]

end OQ14.Packet06AxialActualPhase
#print axioms OQ14.Packet06AxialActualPhase.component_image_ae
#print axioms OQ14.Packet06AxialActualPhase.component_image_general_ae
