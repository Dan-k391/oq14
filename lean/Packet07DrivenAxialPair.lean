import Packet07DrivenAxialTests
import MaterialMaxwell

/-! Actual axial field-pair rotation under locally integrable fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialPair
open MeasureTheory Maxwell DynamicSource MaterialMaxwell ModalAxialRotation Packet07DrivenAxialTests WeakAnnularMoment

def rotateField (θ : ℝ) (F : Field) : Field := fun x => vector θ (F (rotation (-θ) x))

theorem rotated_component_integrable (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i))
    (i : Fin 3) (f : Test) : Integrable (fun x => F (rotation (-θ) x) i*f.val x) := by
  have hi : Integrable (fun x => F x i*(rotateTest θ f).val x) :=
    integrable_mul_compact _ _ (hF i) (rotateTest θ f).val.continuous (rotateTest θ f).property
  have hh := ((rotation (-θ)).measurePreserving.integrable_comp hi.aestronglyMeasurable).mpr hi
  apply hh.congr
  filter_upwards with x
  simp only [Function.comp_apply,rotateTest_apply]
  change F ((rotation (-θ)) x) i*f.val (rotation θ (rotation (-θ) x)) = _
  have hrot : spatial θ (spatial (-θ) x)=x := by simpa using spatial_inverse (-θ) x
  simp [rotation,hrot]

theorem field_pair_zero (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (f : Test) :
    fieldPair (rotateField θ F) 0 f = (Real.cos θ : ℂ)*fieldPair F 0 (rotateTest θ f) -
      (Real.sin θ : ℂ)*fieldPair F 1 (rotateTest θ f) := by
  change (∫ x, ((Real.cos θ : ℂ)*F (rotation (-θ) x) 0-(Real.sin θ : ℂ)*F (rotation (-θ) x) 1)*f.val x) = _
  simp only [sub_mul,mul_assoc]
  rw [integral_sub ((rotated_component_integrable θ F hF 0 f).const_mul _) ((rotated_component_integrable θ F hF 1 f).const_mul _),
    integral_const_mul,integral_const_mul]
  change (Real.cos θ : ℂ)*(∫ x, F (rotation (-θ) x) 0*f.val x) -
    (Real.sin θ : ℂ)*(∫ x, F (rotation (-θ) x) 1*f.val x) = _
  rw [pairing_rotate θ (fun x => F x 0) f,pairing_rotate θ (fun x => F x 1) f]
  rfl

theorem field_pair_one (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (f : Test) :
    fieldPair (rotateField θ F) 1 f = (Real.sin θ : ℂ)*fieldPair F 0 (rotateTest θ f) +
      (Real.cos θ : ℂ)*fieldPair F 1 (rotateTest θ f) := by
  change (∫ x, ((Real.sin θ : ℂ)*F (rotation (-θ) x) 0+(Real.cos θ : ℂ)*F (rotation (-θ) x) 1)*f.val x) = _
  simp only [add_mul,mul_assoc]
  rw [integral_add ((rotated_component_integrable θ F hF 0 f).const_mul _) ((rotated_component_integrable θ F hF 1 f).const_mul _),
    integral_const_mul,integral_const_mul]
  change (Real.sin θ : ℂ)*(∫ x, F (rotation (-θ) x) 0*f.val x) +
    (Real.cos θ : ℂ)*(∫ x, F (rotation (-θ) x) 1*f.val x) = _
  rw [pairing_rotate θ (fun x => F x 0) f,pairing_rotate θ (fun x => F x 1) f]
  rfl

theorem field_pair_two (θ : ℝ) (F : Field) (f : Test) :
    fieldPair (rotateField θ F) 2 f = fieldPair F 2 (rotateTest θ f) := by
  unfold fieldPair rotateField
  simp only [vector,Matrix.cons_val_two,Matrix.head_cons]
  exact pairing_rotate θ (fun x => F x 2) f
end OQ14.Packet07DrivenAxialPair
#print axioms OQ14.Packet07DrivenAxialPair.rotated_component_integrable
#print axioms OQ14.Packet07DrivenAxialPair.field_pair_zero
#print axioms OQ14.Packet07DrivenAxialPair.field_pair_one
#print axioms OQ14.Packet07DrivenAxialPair.field_pair_two
