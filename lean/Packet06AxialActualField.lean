import Packet06AxialOutgoingTransport
import Packet06PlacedMaterialField
import Packet06ComplexElectric
import Packet06AxialAmplitude

/-! On positive material, the literal solved electric response transforms
under arbitrary axial rotation with the physical Cartesian matrix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialActualField
open MeasureTheory Metric Set Maxwell ModalAxialRotation Packet06AxialMaterialTransport
  Packet06AxialOutgoingTransport Packet06PlacedMaterialField

theorem rotated_response_material_ae (θ : ℝ) (c : StaticCoefficient.Coefficient) (z : ℂ) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (i : Fin 3) :
    ∀ᵐ x : Maxwell.Space, c.value (VectorFourier.coordinateMap (rotation (-θ) x)) ≠ 0 →
      Packet06LocalPencil.response (coefficient θ c) z R T (action θ u) (VectorFourier.coordinateMap x) i =
        ∑ j : Fin 3, matrix θ i j * Packet06LocalPencil.response c z R T u
          (VectorFourier.coordinateMap (rotation (-θ) x)) j := by
  obtain ⟨hs,hk,_,_⟩ := rotated_normalized_mode θ c z R hR hc u hu hN
  have hp := kernel_weighted_response_ae (coefficient θ c) z R T hRT (action θ u) hs hk i
  have ho : ∀ j : Fin 3, ∀ᵐ x : Maxwell.Space,
      u (VectorFourier.coordinateMap x) j = (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap x) j :=
    fun j => kernel_weighted_response_ae c z R T hRT u hc hu j
  have hor := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae (ae_all_iff.mpr ho)
  filter_upwards [hp,action_ae θ u i,hor] with x hp' ha ho'
  intro hχ
  have hsqrt : (Real.sqrt (c.value (VectorFourier.coordinateMap (rotation (-θ) x))) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact Real.sqrt_ne_zero'.mpr ((c.nonnegative _).lt_of_ne' hχ)
  rw [Packet06AxialMaterialTransport.coefficient_value] at hp'
  apply mul_left_cancel₀ hsqrt
  rw [← hp',ha]
  simp_rw [ho']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rotated_electric_material_ae (θ : ℝ) (c : StaticCoefficient.Coefficient) (z : ℂ) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (i : Fin 3) :
    ∀ᵐ x : Maxwell.Space, x ∈ closedBall 0 T →
      c.value (VectorFourier.coordinateMap (rotation (-θ) x)) ≠ 0 →
      Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
        (DynamicVolume.source (coefficient θ c) (action θ u)) x i =
      ∑ j : Fin 3, matrix θ i j * Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) (rotation (-θ) x) j := by
  obtain ⟨hs,_,_,_⟩ := rotated_normalized_mode θ c z R hR hc u hu hN
  have hp := Packet06ComplexElectric.electric_ae_on_ball z R T
    (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
    (DynamicVolume.source (coefficient θ c) (action θ u))
    (DynamicVolume.source_integrable (coefficient θ c) (action θ u) R hs)
    (DynamicVolume.source_zero (coefficient θ c) (action θ u) R hs)
    (StaticNewton.material_source_ae (coefficient θ c) (action θ u)) i
  have hp' := (ae_restrict_iff' measurableSet_closedBall).mp hp
  have hb (j : Fin 3) := Packet06ComplexElectric.electric_ae_on_ball z R T
    (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)
    (StaticNewton.material_source_ae c u) j
  have hbr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
    (ae_all_iff.mpr (fun j => (ae_restrict_iff' measurableSet_closedBall).mp (hb j)))
  have ht := rotated_response_material_ae θ c z R T hR hRT hc u hu hN i
  filter_upwards [hp',hbr,ht] with x hp'' hb' ht' hx hpos
  have hx' : rotation (-θ) x ∈ closedBall (0 : Maxwell.Space) T := by
    simpa [mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hx
  have he := hp'' hx
  change Packet06LocalPencil.response (coefficient θ c) z R T (action θ u) (VectorFourier.coordinateMap x) i = _ at he
  rw [← he,ht' hpos]
  apply Finset.sum_congr rfl
  intro j _
  have hj := hb' j hx'
  change Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap (rotation (-θ) x)) j = _ at hj
  rw [hj]
end OQ14.Packet06AxialActualField
#print axioms OQ14.Packet06AxialActualField.rotated_response_material_ae
#print axioms OQ14.Packet06AxialActualField.rotated_electric_material_ae
