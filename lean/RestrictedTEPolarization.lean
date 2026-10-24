import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

/-! Complex polarization for sesquilinear maps (linear in the first slot, conjugate-linear in the second)
with values in an arbitrary complex vector space. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.RestrictedTEPolarization
open Complex
open scoped ComplexConjugate

section Generic
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Plain hypothesis bundle: additive and `ℂ`-homogeneous in the first slot,
additive and conjugate-homogeneous in the second. -/
structure Sesq (B : V → V → W) : Prop where
  add_left : ∀ u u' v, B (u+u') v=B u v+B u' v
  smul_left : ∀ (z : ℂ) u v, B (z • u) v=z • B u v
  add_right : ∀ u v v', B u (v+v')=B u v+B u v'
  smul_right : ∀ (z : ℂ) u v, B u (z • v)=(conj z) • B u v

namespace Sesq
variable {B : V → V → W} (h : Sesq B)
include h

theorem neg_right (u v : V) : B u (-v)=-B u v := by
  have := h.smul_right (-1) u v
  simpa using this

theorem sub_left (u u' v : V) : B (u-u') v=B u v-B u' v := by
  have := h.smul_left (-1) u' v
  rw [sub_eq_add_neg, show -u'=(-1 : ℂ) • u' by simp, h.add_left, this]
  simp [sub_eq_add_neg]

theorem sub_right (u v v' : V) : B u (v-v')=B u v-B u v' := by
  rw [sub_eq_add_neg, h.add_right, h.neg_right, ← sub_eq_add_neg]

theorem diag_add (u v : V) : B (u+v) (u+v)=B u u+B u v+B v u+B v v := by
  rw [h.add_left, h.add_right, h.add_right]
  abel

theorem diag_sub (u v : V) : B (u-v) (u-v)=B u u-B u v-B v u+B v v := by
  rw [h.sub_left, h.sub_right, h.sub_right]
  abel

theorem diag_add_I (u v : V) :
    B (u+I • v) (u+I • v)=B u u+(-I) • B u v+I • B v u+B v v := by
  rw [h.add_left, h.add_right, h.add_right, h.smul_left, h.smul_left, h.smul_right, h.smul_right]
  simp only [Complex.conj_I]
  rw [smul_smul, show I*(-I)=1 by simp]
  rw [one_smul]
  abel

theorem diag_sub_I (u v : V) :
    B (u-I • v) (u-I • v)=B u u+I • B u v+(-I) • B v u+B v v := by
  rw [h.sub_left, h.sub_right, h.sub_right, h.smul_left, h.smul_left, h.smul_right, h.smul_right]
  simp only [Complex.conj_I]
  rw [smul_smul, show I*(-I)=1 by simp]
  rw [one_smul]
  simp only [neg_smul, smul_neg]
  abel

/-- Complex polarization identity. -/
theorem polarization (u v : V) :
    B u v=(1/4 : ℂ) • ((B (u+v) (u+v)-B (u-v) (u-v))+
      I • (B (u+I • v) (u+I • v)-B (u-I • v) (u-I • v))) := by
  rw [h.diag_add, h.diag_sub, h.diag_add_I, h.diag_sub_I]
  have e : ((B u u+B u v+B v u+B v v-(B u u-B u v-B v u+B v v))+
      I • (B u u+(-I) • B u v+I • B v u+B v v-(B u u+I • B u v+(-I) • B v u+B v v)))=
      (4 : ℂ) • B u v := by
    have h1 : I • (B u u+(-I) • B u v+I • B v u+B v v-(B u u+I • B u v+(-I) • B v u+B v v))=
        (2 : ℂ) • B u v-(2 : ℂ) • B v u := by
      have : B u u+(-I) • B u v+I • B v u+B v v-(B u u+I • B u v+(-I) • B v u+B v v)=
          ((-2*I : ℂ)) • B u v+((2*I : ℂ)) • B v u := by
        simp only [neg_smul, mul_smul, two_smul]
        module
      rw [this, smul_add, smul_smul, smul_smul]
      have a1 : I*(-2*I : ℂ)=2 := by ring_nf; simp
      have a2 : I*(2*I : ℂ)=-2 := by ring_nf; simp
      rw [a1, a2, neg_smul, sub_eq_add_neg]
    rw [h1]
    module
  rw [e, smul_smul]
  norm_num

/-- Variant: the sum `B u v + B v u` from two diagonal values. -/
theorem symmetrized (u v : V) :
    B u v+B v u=(1/2 : ℂ) • (B (u+v) (u+v)-B (u-v) (u-v)) := by
  rw [h.diag_add, h.diag_sub]
  module

end Sesq
end Generic

section Scalar
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Scalar-valued polarization with `Q u := B u u`. -/
theorem polarization_complex (B : V → V → ℂ) (h : Sesq B) (u v : V) :
    B u v=(B (u+v) (u+v)-B (u-v) (u-v)+I*(B (u+I • v) (u+I • v)-B (u-I • v) (u-I • v)))/4 := by
  rw [h.polarization u v]
  simp only [smul_eq_mul]
  ring

/-- For a Hermitian form, the real part of `B u v` is recovered from two diagonal values. -/
theorem re_polarization (B : V → V → ℂ) (h : Sesq B) (hherm : ∀ u v, B v u=conj (B u v)) (u v : V) :
    (B u v).re=((B (u+v) (u+v)).re-(B (u-v) (u-v)).re)/4 := by
  have := h.symmetrized u v
  rw [hherm u v, smul_eq_mul] at this
  have hre := congrArg Complex.re this
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.sub_re] at hre
  norm_num at hre
  linarith

end Scalar

end OQ14.RestrictedTEPolarization
#print axioms OQ14.RestrictedTEPolarization.Sesq.polarization
#print axioms OQ14.RestrictedTEPolarization.Sesq.symmetrized
#print axioms OQ14.RestrictedTEPolarization.polarization_complex
#print axioms OQ14.RestrictedTEPolarization.re_polarization
