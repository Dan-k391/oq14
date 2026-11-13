import Packet06GlobalField
import Packet06ComplexElectric

/-! The global outgoing representative and the potential-based electric
field used in the hotspot estimates define the same physical field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06GlobalElectricIdentification
open MeasureTheory Set Metric Maxwell

theorem global_electric_ae (c : StaticCoefficient.Coefficient) (z : ℂ) (S : ℝ)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (i : Fin 3) :
    (fun x => Packet06GlobalField.electric c z S u x i) =ᵐ[volume]
      (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) x i) := by
  have hball (T : ℝ) (hT : S+1 ≤ T) :
      (fun x => Packet06GlobalField.electric c z S u x i) =ᵐ[volume.restrict (closedBall 0 T)]
        (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
          (DynamicVolume.source c u) x i) := by
    have hg := Packet06GlobalField.electric_matches_response c z S T hT u hc i
    have he := Packet06ComplexElectric.electric_ae_on_ball z S T (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
      (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i
    exact hg.trans he
  have hall := ae_all_iff.mpr (fun j : ℕ =>
    (ae_restrict_iff' measurableSet_closedBall).mp (hball (max (j : ℝ) (S+1)) (le_max_right _ _)))
  filter_upwards [hall] with x hx
  obtain ⟨j,hj⟩ := exists_nat_gt ‖x‖
  apply hx j
  simpa only [mem_closedBall,dist_zero_right] using
    (show ‖x‖ ≤ max (j : ℝ) (S+1) from hj.le.trans (le_max_left _ _))

theorem global_phase_representative (c : StaticCoefficient.Coefficient) (z : ℂ) (S : ℝ)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (A : Set Space) (R : Fin 3 → Space → ℂ)
    (hR : ∀ i, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x i) =ᵐ[volume.restrict A] R i) :
    ∀ i, (fun x => Packet06GlobalField.electric c z S u x i) =ᵐ[volume.restrict A] R i := by
  intro i
  have he : (fun x => Packet06GlobalField.electric c z S u x i) =ᵐ[volume.restrict A]
      (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) x i) := ae_restrict_of_ae (global_electric_ae c z S u hc i)
  exact he.trans (hR i)

end OQ14.Packet06GlobalElectricIdentification
#print axioms OQ14.Packet06GlobalElectricIdentification.global_electric_ae
#print axioms OQ14.Packet06GlobalElectricIdentification.global_phase_representative
