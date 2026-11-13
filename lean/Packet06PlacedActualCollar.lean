import Packet06PlacedActualPhase

/-! Open physical collar bounds for the actual field, preserved by normalized
placement in addition to the boundary-sphere bound of a hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedActualCollar
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet06PlacementHomeomorph
  Packet06PlacedPhaseField Packet06PlacedKernel Packet06CyclicRotation

def HasPhysicalCollar (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (center : Space) (r B : ℝ) : Prop :=
  ∃ A : Set Space, IsOpen A ∧ sphere center r ⊆ A ∧
    ∀ᵐ x ∂volume.restrict A, physicalAmplitude (fun k y => Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) y k) x ≤ B

theorem placed_collar (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (s : ℝ) (hs : 0 < s) (a center : Space) (r B : ℝ)
    (A : Set Space) (hA : IsOpen A) (hAsphere : sphere center r ⊆ A)
    (hAunit : A ⊆ ball (0 : Space) 1)
    (hbound : ∀ᵐ x ∂volume.restrict A, physicalAmplitude (fun k y => Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) y k) x ≤ B) :
    HasPhysicalCollar (placedCoefficient s a c) ((s : ℂ)*z) (placedUnknown s a u)
      (placement s hs a center) (r/s) (scale s*B) := by
  let h := placement s hs a
  have hq : Measure.QuasiMeasurePreserving h.symm volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [h,placement,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hb := hq.ae ((ae_restrict_iff' hA.measurableSet).mp hbound)
  let E : Fin 3 → Space → ℂ := fun k y => Packet06ComplexElectric.electric z
    (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) y k
  have he := Packet06PlacedActualPhase.component_target_ae c hc hpos z u hu hN s hs a A
    hA.measurableSet E (fun _ => Filter.EventuallyEq.rfl)
  have hall := ae_all_iff.mpr he
  have himg : IsOpen (h '' A) := h.isOpenMap _ hA
  refine ⟨h '' A,himg,?_,?_⟩
  · intro y hy
    have hd := Packet06PlanarProjection.point_distance_pair s hs a (h.symm y) center
    change dist (h (h.symm y)) (h center)=_ at hd
    rw [h.apply_symm_apply, show dist y (h center)=r/s from hy,
      div_eq_mul_inv,mul_comm r s⁻¹] at hd
    have hsource : h.symm y ∈ sphere center r := (mul_left_cancel₀ (inv_ne_zero hs.ne') hd).symm
    exact ⟨h.symm y,hAsphere hsource,h.apply_symm_apply y⟩
  · apply (ae_restrict_iff' himg.measurableSet).mpr
    filter_upwards [hb,hall] with y hby hey hy
    have hback : h.symm y ∈ A := by rwa [h.image_eq_preimage] at hy
    have hamp : physicalAmplitude (fun k x => Packet06ComplexElectric.electric ((s : ℂ)*z)
        (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
        (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u)) x k) y =
        physicalAmplitude (transport s hs a E) y := by
      simp only [physicalAmplitude]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => by rw [hey k hback (hAunit hback)])
    rw [hamp,amplitude_transport]
    exact mul_le_mul_of_nonneg_left (hby hback) (scale_pos s hs).le

end OQ14.Packet06PlacedActualCollar
#print axioms OQ14.Packet06PlacedActualCollar.placed_collar
