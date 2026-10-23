import ParityDensityWeak
import WeakMaxwellLinear

/-! Derived modified incident pair and actual weighted datum for the parity material inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityModifiedIncident
open MeasureTheory Maxwell MaterialMaxwell
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def electric (c : Coefficient) (k B : ℝ) (u : VectorL2) (E : Field) : Field :=
  fun x i => E x i+((B^2-1 : ℝ) : ℂ)*ParityPlaneFields.electric true k (DynamicVolume.source c u) x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*ParityPlaneFields.electric false k (DynamicVolume.source c u) x i

def magnetic (c : Coefficient) (k B : ℝ) (u : VectorL2) (H : Field) : Field :=
  fun x i => H x i+((B^2-1 : ℝ) : ℂ)*ParityPlaneFields.magnetic true k (DynamicVolume.source c u) x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*ParityPlaneFields.magnetic false k (DynamicVolume.source c u) x i

theorem locallyIntegrable (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (u : VectorL2) (E H : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i)) :
    (∀ i, LocallyIntegrable (fun x => electric c k B u E x i)) ∧
    (∀ i, LocallyIntegrable (fun x => magnetic c k B u H x i)) := by
  have hr := DynamicVolume.source_integrable c u d.radius d.ballZero
  constructor
  · intro i
    exact ((hE i).add (continuous_const.mul (ParityPlaneFields.electric_continuous true k _ hr i)).locallyIntegrable).add
      (continuous_const.mul (ParityPlaneFields.electric_continuous false k _ hr i)).locallyIntegrable
  · intro i
    exact ((hH i).add (continuous_const.mul (ParityPlaneFields.magnetic_continuous true k _ hr i)).locallyIntegrable).add
      (continuous_const.mul (ParityPlaneFields.magnetic_continuous false k _ hr i)).locallyIntegrable

theorem testMaxwell (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (u : VectorL2) (E H : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hm : TestMaxwell k (fun _ => 1) E H) :
    TestMaxwell k (fun _ => 1) (electric c k B u E) (magnetic c k B u H) := by
  let ρ := DynamicVolume.source c u
  let ze : ℂ := ((B^2-1 : ℝ) : ℂ)
  let zm : ℂ := ((B⁻¹^2-1 : ℝ) : ℂ)
  have hr := DynamicVolume.source_integrable c u d.radius d.ballZero
  have hET (i : Fin 3) : LocallyIntegrable (fun x => ze*ParityPlaneFields.electric true k ρ x i) :=
    (continuous_const.mul (ParityPlaneFields.electric_continuous true k ρ hr i)).locallyIntegrable
  have hHT (i : Fin 3) : LocallyIntegrable (fun x => ze*ParityPlaneFields.magnetic true k ρ x i) :=
    (continuous_const.mul (ParityPlaneFields.magnetic_continuous true k ρ hr i)).locallyIntegrable
  have hEF (i : Fin 3) : LocallyIntegrable (fun x => zm*ParityPlaneFields.electric false k ρ x i) :=
    (continuous_const.mul (ParityPlaneFields.electric_continuous false k ρ hr i)).locallyIntegrable
  have hHF (i : Fin 3) : LocallyIntegrable (fun x => zm*ParityPlaneFields.magnetic false k ρ x i) :=
    (continuous_const.mul (ParityPlaneFields.magnetic_continuous false k ρ hr i)).locallyIntegrable
  have ht := WeakMaxwellLinear.smul_vacuum k ze _ _ (ParityDensityWeak.testMaxwell true k ρ hr)
  have hf := WeakMaxwellLinear.smul_vacuum k zm _ _ (ParityDensityWeak.testMaxwell false k ρ hr)
  have hh := WeakMaxwellLinear.add_vacuum k E H _ _ hE hH hET hHT hm ht
  exact WeakMaxwellLinear.add_vacuum k _ _ _ _ (fun i => (hE i).add (hET i)) (fun i => (hH i).add (hHT i)) hEF hHF hh hf

theorem weighted_datum (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (u f : VectorL2) (E : Field)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i)
    (hsol : ParityMaterialField.block d k B u=f) (i : Fin 3) :
    (fun x => DynamicVolume.volumeBlock c k d.radius u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*electric c k B u E x i := by
  filter_upwards [ParityMaterialField.block_actual d k B u i,
    DynamicVolume.volumeBlock_actual c u k d.radius d.ballZero i,
    MaterialField.scattered_actual c k u i,hincident i] with x hx hv hs hi
  rw [hsol,hi] at hx
  rw [← hs] at hv
  rw [hv]
  unfold ParityMaterialField.scattered at hx
  simp only [electric,ParityPlaneFields.electric_material]
  linear_combination -hx

end OQ14.ParityModifiedIncident
#print axioms OQ14.ParityModifiedIncident.locallyIntegrable
#print axioms OQ14.ParityModifiedIncident.testMaxwell
#print axioms OQ14.ParityModifiedIncident.weighted_datum
