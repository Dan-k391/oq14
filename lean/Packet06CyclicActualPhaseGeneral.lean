import Packet06PlacedActualPhase

/-! Cyclic physical electric transport with arbitrary support radius and
positivity required only on the observation set. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06CyclicActualPhaseGeneral
open MeasureTheory Metric Set Maxwell Packet06PlacedKernel Packet06CyclicRotation
  Packet06PlacedPhaseField Packet06PlacementHomeomorph
open scoped Topology
abbrev Space := Maxwell.Space

theorem component_image_general_ae (c : StaticCoefficient.Coefficient) (R T : ℝ)
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
      (StaticCoefficient.sqrtMultiplier (placedCoefficient 1 0 c) (placedUnknown 1 0 u))
      (DynamicVolume.source (placedCoefficient 1 0 c) (placedUnknown 1 0 u)) y i) =ᵐ[
      volume.restrict (placement 1 (by norm_num) 0 '' V)] transport 1 (by norm_num) 0 reps i := by
  let h := placement 1 (by norm_num) 0
  have hset : MeasurableSet (h '' V) := by
    change MeasurableSet (h.toEquiv '' V)
    rw [h.toEquiv.image_eq_preimage]
    exact hV.preimage h.symm.continuous.measurable
  have hr := (rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    ((ae_restrict_iff' hV).mp (hreps (WeakCurl.previous i))))
  have he := Packet06PlacedActualField.electric_ae c R T hR hRT hc z u hu hN 1 (by norm_num) 0 T
    (by simpa using hRT) i
  apply (ae_restrict_iff' hset).mpr
  filter_upwards [hr,he] with y hr he hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hyT : h x ∈ closedBall (0 : Space) T := by
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right,rotate_norm] using hVball hx
  have hinv : unrotate (h x) = x := by
    simpa [h,placement,Packet06PhysicalPlacement.point] using unrotate_rotate x
  have hp : c.value (VectorFourier.coordinateMap (unrotate ((1 : ℝ) • (h x-0)))) ≠ 0 := by
    simpa [hinv] using hpos x hx
  have he' := he hyT (by simpa [hinv] using hVball hx) hp
  change unrotate (h x) ∈ V → _ at hr
  have hre := hr (by simpa [hinv] using hx)
  change Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (unrotate (h x)) (WeakCurl.previous i) = reps (WeakCurl.previous i) (unrotate (h x)) at hre
  rw [hinv] at hre
  simp only [one_smul,sub_zero,hinv,Complex.ofReal_one,one_mul,Real.sqrt_one] at he'
  rw [hre] at he'
  simpa [transport,scale,h,placement,Packet06PhysicalPlacement.point,unrotate_rotate] using he'

end OQ14.Packet06CyclicActualPhaseGeneral
#print axioms OQ14.Packet06CyclicActualPhaseGeneral.component_image_general_ae
