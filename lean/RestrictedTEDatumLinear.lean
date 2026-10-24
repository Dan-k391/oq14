import RestrictedTEFieldLinear

/-! The actual sqrt-chi harmonic datum and literal material inverse are complex-linear. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEDatumLinear
open MeasureTheory Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem physical_ext (u v : VectorL2)
    (h : ∀ i : Fin 3, (fun x : Space => u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => v (VectorFourier.coordinateMap x) i) : u=v := by
  apply Lp.ext
  have hp : ∀ᵐ x : Space, u (VectorFourier.coordinateMap x)=v (VectorFourier.coordinateMap x) := by
    filter_upwards [ae_all_iff.mpr h] with x hx
    apply PiLp.ext
    intro i
    exact hx i
  have hn := (MeasurePreserving.symm VectorFourier.coordinateMap
    VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae hp
  simpa only [Function.comp_apply,MeasurableEquiv.apply_symm_apply] using hn

theorem datum_add (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A B : Index →₀ ℂ) :
    RestrictedTEMaterial.datum c d (A+B)=RestrictedTEMaterial.datum c d A+RestrictedTEMaterial.datum c d B := by
  apply physical_ext
  intro i
  have hc := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (RestrictedTEMaterial.datum c d A) (RestrictedTEMaterial.datum c d B))
  filter_upwards [RestrictedTEMaterial.datum_actual c d (A+B) i,
    RestrictedTEMaterial.datum_actual c d A i,RestrictedTEMaterial.datum_actual c d B i,hc] with x hs ha hb hc
  rw [hs,hc]
  simp only [Pi.add_apply,PiLp.add_apply]
  rw [ha,hb,RestrictedTEFieldLinear.electric_add]
  simp only [Pi.add_apply]
  ring

theorem datum_smul (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (z : ℂ) (A : Index →₀ ℂ) :
    RestrictedTEMaterial.datum c d (z • A)=z • RestrictedTEMaterial.datum c d A := by
  apply physical_ext
  intro i
  have hc := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul z (RestrictedTEMaterial.datum c d A))
  filter_upwards [RestrictedTEMaterial.datum_actual c d (z • A) i,RestrictedTEMaterial.datum_actual c d A i,hc]
    with x hs ha hc
  rw [hs,hc]
  simp only [Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
  rw [ha,RestrictedTEScale.electric_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def datumMap (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) : (Index →₀ ℂ) →ₗ[ℂ] VectorL2 where
  toFun := RestrictedTEMaterial.datum c d
  map_add' := datum_add c d
  map_smul' := datum_smul c d

def solutionMap (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (B : ℝ) :
    (Index →₀ ℂ) →ₗ[ℂ] VectorL2 :=
  (Ring.inverse (ParityMaterialField.block d 1 B)).toLinearMap.comp (datumMap c d)

theorem solutionMap_apply (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (B : ℝ)
    (A : Index →₀ ℂ) : solutionMap c d B A=
      ParityMaterialField.solution d 1 B (RestrictedTEMaterial.datum c d A) := rfl

end OQ14.RestrictedTEDatumLinear
#print axioms OQ14.RestrictedTEDatumLinear.physical_ext
#print axioms OQ14.RestrictedTEDatumLinear.datum_add
#print axioms OQ14.RestrictedTEDatumLinear.datum_smul
#print axioms OQ14.RestrictedTEDatumLinear.solutionMap_apply
