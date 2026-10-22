import ParityPlaneFields
import HerglotzParityPlane

/-! Actual parity density flux columns and their integrability. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityPlaneColumns
open MeasureTheory Metric ParityPlaneFields PlaneSourceKernel MaxwellRadiation
open SphereReactionKernel (reaction)
open SphereMagneticParity (magneticReaction)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
open Maxwell (conjugate)
open scoped ComplexConjugate

theorem electric_cross (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (v : Vector) :
    crossProduct (ParityPlaneFields.electric e k ρ x) (conjugate v) 2=
      ∑ j : Fin 3, ∫ y, ρ j y*crossProduct (fun i => reaction e k x y i j) (conjugate v) 2 := by
  change (∑ j : Fin 3, ∫ y, reaction e k x y 0 j*ρ j y)*star (v 1)-
    (∑ j : Fin 3, ∫ y, reaction e k x y 1 j*ρ j y)*star (v 0)=_
  rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_mul_const,← integral_mul_const,
    ← integral_sub ((electric_integrand e k ρ hρ x 0 j).mul_const _)
      ((electric_integrand e k ρ hρ x 1 j).mul_const _)]
  apply integral_congr_ae
  filter_upwards with y
  change (reaction e k x y 0 j*ρ j y)*star (v 1)-(reaction e k x y 1 j*ρ j y)*star (v 0)=
    ρ j y*(reaction e k x y 0 j*star (v 1)-reaction e k x y 1 j*star (v 0))
  ring

theorem electric_cross_integrable (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (v : Vector) (j : Fin 3) :
    Integrable (fun y => ρ j y*crossProduct (fun i => reaction e k x y i j) (conjugate v) 2) := by
  apply (((electric_integrand e k ρ hρ x 0 j).mul_const (star (v 1))).sub
    ((electric_integrand e k ρ hρ x 1 j).mul_const (star (v 0)))).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  change (reaction e k x y 0 j*ρ j y)*star (v 1)-(reaction e k x y 1 j*ρ j y)*star (v 0)=
    ρ j y*(reaction e k x y 0 j*star (v 1)-reaction e k x y 1 j*star (v 0))
  ring

private theorem conj_integrable {f : Space → ℂ} (hf : Integrable f) : Integrable (fun y => conj (f y)) :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

theorem magnetic_cross (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (v : Vector) :
    crossProduct v (conjugate (ParityPlaneFields.magnetic e k ρ x)) 2=
      ∑ j : Fin 3, ∫ y, conj (ρ j y)*crossProduct v
        (conjugate (fun i => magneticReaction e k x y i j)) 2 := by
  change v 0*star (∑ j : Fin 3, ∫ y, magneticReaction e k x y 1 j*ρ j y)-
    v 1*star (∑ j : Fin 3, ∫ y, magneticReaction e k x y 0 j*ρ j y)=_
  simp only [star_sum,Complex.star_def]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_conj,← integral_conj,← integral_const_mul,← integral_const_mul,
    ← integral_sub ((conj_integrable (magnetic_integrand e k ρ hρ x 1 j)).const_mul _)
      ((conj_integrable (magnetic_integrand e k ρ hρ x 0 j)).const_mul _)]
  apply integral_congr_ae
  filter_upwards with y
  change v 0*conj (magneticReaction e k x y 1 j*ρ j y)-
    v 1*conj (magneticReaction e k x y 0 j*ρ j y)=_
  simp [cross_apply,conjugate,map_mul]
  ring

theorem magnetic_cross_integrable (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (v : Vector) (j : Fin 3) :
    Integrable (fun y => conj (ρ j y)*crossProduct v
      (conjugate (fun i => magneticReaction e k x y i j)) 2) := by
  apply (((conj_integrable (magnetic_integrand e k ρ hρ x 1 j)).const_mul (v 0)).sub
    ((conj_integrable (magnetic_integrand e k ρ hρ x 0 j)).const_mul (v 1))).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  simp [cross_apply,conjugate,map_mul]
  ring

theorem sum_integral_bound (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (f : Fin 3 → Space → ℂ) (hi : ∀ j, Integrable (f j)) (C : ℝ)
    (hb : ∀ j, ∀ᵐ y, ‖f j y‖ ≤ C*‖ρ j y‖) :
    ‖∑ j : Fin 3, ∫ y, f j y‖ ≤ C*sourceMass ρ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ∫ y, ‖f j y‖ := Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm _)
    _ ≤ ∑ j : Fin 3, C*(∫ y, ‖ρ j y‖) := Finset.sum_le_sum (fun j _ =>
      (integral_mono_ae (hi j).norm ((hρ j).norm.const_mul C) (hb j)).trans_eq (integral_const_mul _ _))
    _ = _ := by unfold sourceMass; rw [Finset.mul_sum]

end OQ14.ParityPlaneColumns
#print axioms OQ14.ParityPlaneColumns.electric_cross
#print axioms OQ14.ParityPlaneColumns.electric_cross_integrable
#print axioms OQ14.ParityPlaneColumns.magnetic_cross
#print axioms OQ14.ParityPlaneColumns.magnetic_cross_integrable
#print axioms OQ14.ParityPlaneColumns.sum_integral_bound
