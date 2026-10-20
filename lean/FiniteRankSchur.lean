import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Abel

/-! # Typed finite-rank Schur reduction and the Woodbury inverse

The algebra holds for arbitrary normed spaces; finite dimensionality of the
auxiliary space is needed only for later determinant arguments. No compact
operator or analytic Fredholm conclusion is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.FiniteRankSchur

variable {𝕜 E V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

def large (U : V →L[𝕜] E) (B : E →L[𝕜] V) : E →L[𝕜] E := 1-U.comp B

def small (U : V →L[𝕜] E) (B : E →L[𝕜] V) : V →L[𝕜] V := 1-B.comp U

def liftedInverse (U : V →L[𝕜] E) (B : E →L[𝕜] V) : E →L[𝕜] E :=
  1+U.comp ((Ring.inverse (small U B)).comp B)

theorem large_liftedInverse (U : V →L[𝕜] E) (B : E →L[𝕜] V)
    (hD : IsUnit (small U B)) : large U B * liftedInverse U B = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T : V →L[𝕜] V => T (B x))
    (Ring.mul_inverse_cancel (small U B) hD)
  change Ring.inverse (small U B) (B x)-B (U (Ring.inverse (small U B) (B x))) = B x at h
  have he : B x+B (U (Ring.inverse (small U B) (B x))) =
      Ring.inverse (small U B) (B x) := (eq_add_of_sub_eq h).symm
  change x+U (Ring.inverse (small U B) (B x))-
    U (B (x+U (Ring.inverse (small U B) (B x)))) = x
  rw [map_add, he]
  abel

theorem liftedInverse_large (U : V →L[𝕜] E) (B : E →L[𝕜] V)
    (hD : IsUnit (small U B)) : liftedInverse U B * large U B = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T : V →L[𝕜] V => T (B x))
    (Ring.inverse_mul_cancel (small U B) hD)
  change Ring.inverse (small U B) (B x-B (U (B x))) = B x at h
  change x-U (B x)+U (Ring.inverse (small U B) (B (x-U (B x)))) = x
  rw [map_sub, h]
  abel

theorem large_isUnit_of_small (U : V →L[𝕜] E) (B : E →L[𝕜] V)
    (hD : IsUnit (small U B)) : IsUnit (large U B) := by
  exact ⟨⟨large U B, liftedInverse U B, large_liftedInverse U B hD,
    liftedInverse_large U B hD⟩,rfl⟩

theorem large_isUnit_iff_small (U : V →L[𝕜] E) (B : E →L[𝕜] V) :
    IsUnit (large U B) ↔ IsUnit (small U B) :=
  ⟨fun h => large_isUnit_of_small B U h, large_isUnit_of_small U B⟩

theorem inverse_large (U : V →L[𝕜] E) (B : E →L[𝕜] V)
    (hD : IsUnit (small U B)) : Ring.inverse (large U B) = liftedInverse U B := by
  have hF := large_isUnit_of_small U B hD
  calc
    Ring.inverse (large U B) = Ring.inverse (large U B)*1 := by rw [mul_one]
    _ = Ring.inverse (large U B)*(large U B*liftedInverse U B) := by
      rw [large_liftedInverse U B hD]
    _ = liftedInverse U B := by
      rw [← mul_assoc, Ring.inverse_mul_cancel (large U B) hF, one_mul]

def schur (A : E →L[𝕜] E) (I : V →L[𝕜] E) (B : E →L[𝕜] V) : V →L[𝕜] V :=
  1-B.comp ((Ring.inverse A).comp I)

def woodbury (A : E →L[𝕜] E) (I : V →L[𝕜] E) (B : E →L[𝕜] V) : E →L[𝕜] E :=
  Ring.inverse A+(Ring.inverse A).comp
    (I.comp ((Ring.inverse (schur A I B)).comp (B.comp (Ring.inverse A))))

theorem factorization (A : E →L[𝕜] E) (hA : IsUnit A)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) :
    A-I.comp B = A*large ((Ring.inverse A).comp I) B := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T : E →L[𝕜] E => T (I (B x))) (Ring.mul_inverse_cancel A hA)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply, large, ContinuousLinearMap.one_apply, map_sub, h]

/-- Invertibility of the Banach-space perturbation is exactly invertibility
of its auxiliary-space Schur operator. -/
theorem isUnit_iff_schur (A : E →L[𝕜] E) (hA : IsUnit A)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) :
    IsUnit (A-I.comp B) ↔ IsUnit (schur A I B) := by
  constructor
  · intro hF
    have hL : IsUnit (large ((Ring.inverse A).comp I) B) := by
      have h := hA.ringInverse.mul hF
      rw [factorization A hA I B, ← mul_assoc, Ring.inverse_mul_cancel A hA, one_mul] at h
      exact h
    exact (large_isUnit_iff_small ((Ring.inverse A).comp I) B).mp hL
  · intro hD
    rw [factorization A hA I B]
    exact hA.mul (large_isUnit_of_small ((Ring.inverse A).comp I) B hD)

theorem woodbury_eq_product (A : E →L[𝕜] E)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) :
    woodbury A I B = liftedInverse ((Ring.inverse A).comp I) B * Ring.inverse A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [woodbury, liftedInverse, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  rfl

theorem perturbation_woodbury (A : E →L[𝕜] E) (hA : IsUnit A)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) (hD : IsUnit (schur A I B)) :
    (A-I.comp B)*woodbury A I B = 1 := by
  rw [factorization A hA I B, woodbury_eq_product, mul_assoc,
    ← mul_assoc (large _ _) (liftedInverse _ _), large_liftedInverse _ _ hD,
    one_mul, Ring.mul_inverse_cancel A hA]

theorem woodbury_perturbation (A : E →L[𝕜] E) (hA : IsUnit A)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) (hD : IsUnit (schur A I B)) :
    woodbury A I B*(A-I.comp B) = 1 := by
  rw [factorization A hA I B, woodbury_eq_product,
    mul_assoc, ← mul_assoc (Ring.inverse A) A, Ring.inverse_mul_cancel A hA,
    one_mul, liftedInverse_large _ _ hD]

theorem inverse_woodbury (A : E →L[𝕜] E) (hA : IsUnit A)
    (I : V →L[𝕜] E) (B : E →L[𝕜] V) (hD : IsUnit (schur A I B)) :
    Ring.inverse (A-I.comp B) = woodbury A I B := by
  have hF := (isUnit_iff_schur A hA I B).mpr hD
  calc
    Ring.inverse (A-I.comp B) = Ring.inverse (A-I.comp B)*1 := by rw [mul_one]
    _ = Ring.inverse (A-I.comp B)*((A-I.comp B)*woodbury A I B) := by
      rw [perturbation_woodbury A hA I B hD]
    _ = woodbury A I B := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hF, one_mul]

end OQ14.FiniteRankSchur

#print axioms OQ14.FiniteRankSchur.large_liftedInverse
#print axioms OQ14.FiniteRankSchur.liftedInverse_large
#print axioms OQ14.FiniteRankSchur.large_isUnit_of_small
#print axioms OQ14.FiniteRankSchur.large_isUnit_iff_small
#print axioms OQ14.FiniteRankSchur.inverse_large
#print axioms OQ14.FiniteRankSchur.factorization
#print axioms OQ14.FiniteRankSchur.isUnit_iff_schur
#print axioms OQ14.FiniteRankSchur.woodbury_eq_product
#print axioms OQ14.FiniteRankSchur.perturbation_woodbury
#print axioms OQ14.FiniteRankSchur.woodbury_perturbation
#print axioms OQ14.FiniteRankSchur.inverse_woodbury
