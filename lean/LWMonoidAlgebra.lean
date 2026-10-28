/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Algebra helpers ported from mathlib PR 28013,
commit d173f68c80a51efe617648e78fa1ae3e2b994a9d. -/
noncomputable section
open Finsupp hiding single mapDomain
open scoped AddMonoidAlgebra
namespace AddMonoidAlgebra
variable (k A : Type*) {G : Type*}
variable [CommSemiring k] [Semiring A] [Algebra k A] [AddMonoid G]

@[simps]
def domCongrAut : AddAut G →* A[G] ≃ₐ[k] A[G] where
  toFun := AddMonoidAlgebra.domCongr k A
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- If `f : R →ₐ[k] S` is an algebra homomorphism between two `k`-algebras, then
`Finsupp.mapRange f` is an algebra homomorphism between their additive monoid algebras. -/
def mapRangeAlgHom {k R S G} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] {F} [FunLike F R S] [AlgHomClass F k R S] (f : F) :
    R[G] →ₐ[k] S[G] :=
  liftNCAlgHom (singleZeroAlgHom.comp f) (of S G) (fun _ _ ↦ by
    dsimp [Commute, SemiconjBy]
    rw [single_mul_single, single_mul_single, zero_add, mul_one, add_zero, one_mul])

@[simp]
lemma mapRangeAlgHom_apply {k R S G} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] (f : R →ₐ[k] S) :
      ⇑(mapRangeAlgHom (G := G) f) = Finsupp.mapRange f (map_zero _) := by
  ext x
  induction' x using Finsupp.induction with a b f _ _ ih
  · simp
  · rw [map_add, mapRange_add (map_add _), add_apply, ih]
    erw [liftAddHom_apply_single]
    simp [single_mul_single]

@[simp]
lemma mapRangeAlgHom_id {k R G} [CommSemiring k] [Semiring R] [Algebra k R] [AddMonoid G] :
    mapRangeAlgHom (AlgHom.id k R) = AlgHom.id k R[G] := by
  ext; simp

@[simp]
lemma mapRangeAlgHom_comp {k R S T G} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [Semiring T] [Algebra k T] [AddMonoid G] (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    mapRangeAlgHom (G := G) (g.comp f) =
      (mapRangeAlgHom (G := G) g).comp (mapRangeAlgHom (G := G) f) := by
  ext; simp

theorem lift_mapRangeAlgHom_algebraMap {R S G A}
    [CommSemiring R] [CommSemiring S]
    [AddMonoid G] [Semiring A] [Algebra R A] [Algebra S A] [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative G →* A) (x : R[G]) :
    lift _ _ _ f (mapRangeAlgHom (algebraMap R S).toNatAlgHom x) = lift _ _ _ f x := by
  rw [lift_apply, AddMonoidAlgebra.mapRangeAlgHom_apply, Finsupp.sum_mapRange_index (by simp)]
  simp [lift_apply]

/-- If `f : R ≃ₐ[k] S` is an algebra equivalence between two `k`-algebras, then
`Finsupp.mapRange f` is an algebra equivalence between their additive monoid algebras. -/
@[simps!]
def mapRangeAlgEquiv {k R S G} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] {F} [EquivLike F R S] [AlgEquivClass F k R S] (f : F) :
    R[G] ≃ₐ[k] S[G] :=
  AlgEquiv.ofAlgHom
    (mapRangeAlgHom (AlgEquiv.toAlgHom f))
    (mapRangeAlgHom (AlgEquiv.symm f).toAlgHom)
    (by simp [← mapRangeAlgHom_comp])
    (by simp [← mapRangeAlgHom_comp])

@[simps]
def mapRangeAlgAut {k R G} [CommSemiring k] [Semiring R] [Algebra k R] [AddMonoid G] :
    (R ≃ₐ[k] R) →* R[G] ≃ₐ[k] R[G] where
  toFun f := mapRangeAlgEquiv f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end AddMonoidAlgebra

namespace OQ14.LWMonoidAlgebra
theorem lift_scalar_extension {R S G A : Type*}
    [CommSemiring R] [CommSemiring S] [AddMonoid G] [Semiring A]
    [Algebra R A] [Algebra S A] [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative G →* A) (x : R[G]) :
    AddMonoidAlgebra.lift _ _ _ f
      (AddMonoidAlgebra.mapRangeAlgHom (algebraMap R S).toNatAlgHom x) =
      AddMonoidAlgebra.lift _ _ _ f x :=
  AddMonoidAlgebra.lift_mapRangeAlgHom_algebraMap f x
end OQ14.LWMonoidAlgebra

#print axioms OQ14.LWMonoidAlgebra.lift_scalar_extension
