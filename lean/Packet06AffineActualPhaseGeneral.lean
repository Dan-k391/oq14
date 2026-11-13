import Packet06PlacedActualPhase

/-! Actual electric phase transport under a proper cyclic rotation followed
by arbitrary translation, with positivity only on the observation region. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AffineActualPhaseGeneral
open MeasureTheory Metric Set Maxwell Packet06PlacedKernel Packet06CyclicRotation
  Packet06PlacedPhaseField Packet06PlacementHomeomorph
open scoped Topology
abbrev Space := Maxwell.Space

theorem component_image_general_ae (c : StaticCoefficient.Coefficient) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (a : Space)
    (V : Set Space) (hV : MeasurableSet V) (hVball : V ⊆ closedBall 0 T)
    (hpos : ∀ x ∈ V, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict V] reps i) (i : Fin 3) :
    (fun y => Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier (placedCoefficient 1 a c) (placedUnknown 1 a u))
      (DynamicVolume.source (placedCoefficient 1 a c) (placedUnknown 1 a u)) y i) =ᵐ[
      volume.restrict (placement 1 (by norm_num) a '' V)] transport 1 (by norm_num) a reps i := by
  let h := placement 1 (by norm_num) a
  let q : Space → Space := fun y => unrotate (y-a)
  have hset : MeasurableSet (h '' V) := by
    change MeasurableSet (h.toEquiv '' V)
    rw [h.toEquiv.image_eq_preimage]
    exact hV.preimage h.symm.continuous.measurable
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp ht
  have hr := hq.ae ((ae_restrict_iff' hV).mp (hreps (WeakCurl.previous i)))
  have he := Packet06PlacedActualField.electric_ae c R T hR hRT hc z u hu hN 1 (by norm_num) a
    (T+‖a‖) (by simpa using add_le_add_right hRT ‖a‖) i
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hr,he] with y hr he hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hinv : q (h x) = x := by
    simp [q,h,placement,Packet06PhysicalPlacement.point,unrotate_rotate]
  have hyT : h x ∈ closedBall (0 : Space) (T+‖a‖) := by
    have hxT : ‖x‖ ≤ T := by simpa only [mem_closedBall,dist_zero_right] using hVball hx
    have hh := norm_add_le a (rotate x)
    rw [rotate_norm] at hh
    have hb : ‖a+rotate x‖ ≤ T+‖a‖ := by linarith
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right] using hb
  have hxT : unrotate ((1 : ℝ) • (h x-a)) ∈ closedBall (0 : Space) T := by
    simp only [one_smul]
    change q (h x) ∈ closedBall (0 : Space) T
    rw [hinv]
    exact hVball hx
  have hp : c.value (VectorFourier.coordinateMap (unrotate ((1 : ℝ) • (h x-a)))) ≠ 0 := by
    simp only [one_smul]
    change c.value (VectorFourier.coordinateMap (q (h x))) ≠ 0
    rw [hinv]
    exact hpos x hx
  have he' := he hyT hxT hp
  have hre := hr (by simpa only [hinv] using hx)
  change Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (q (h x)) (WeakCurl.previous i) = reps (WeakCurl.previous i) (q (h x)) at hre
  rw [hinv] at hre
  simp only [one_smul,Complex.ofReal_one,one_mul,Real.sqrt_one] at he'
  change _ = Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (q (h x)) (WeakCurl.previous i) at he'
  rw [hinv,hre] at he'
  simpa [transport,scale,h,placement,Packet06PhysicalPlacement.point,unrotate_rotate] using he'

end OQ14.Packet06AffineActualPhaseGeneral
#print axioms OQ14.Packet06AffineActualPhaseGeneral.component_image_general_ae
