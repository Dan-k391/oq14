import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.FiniteDimensionalDeterminant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def determinant (A : V →L[ℂ] V) : ℂ := LinearMap.det A.toLinearMap

theorem coordinate_analyticAt {ι : Type*} [Fintype ι] (b : Basis ι ℂ V)
    (A : ℂ → V →L[ℂ] V) (z : ℂ) (hA : AnalyticAt ℂ A z) (i j : ι) :
    AnalyticAt ℂ (fun w => b.repr (A w (b j)) i) z := by
  have hc : AnalyticAt ℂ (fun v : V => b.repr v i) (A z (b j)) :=
    ((b.coord i).toContinuousLinearMap).analyticAt (A z (b j))
  have he : AnalyticAt ℂ (fun L : V →L[ℂ] V => L (b j)) (A z) :=
    (ContinuousLinearMap.apply ℂ V (b j)).analyticAt (A z)
  exact hc.comp (f := fun w : ℂ => A w (b j)) (he.comp (f := A) hA)

theorem determinant_analyticAt (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) : AnalyticAt ℂ (fun w => determinant (A w)) z := by
  classical
  let b := Module.finBasis ℂ V
  have hm : AnalyticAt ℂ (fun w => (LinearMap.toMatrix b b (A w).toLinearMap).det) z := by
    simp_rw [Matrix.det_apply']
    apply Finset.analyticAt_sum
    intro σ _
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_prod
    intro i _
    simpa only [LinearMap.toMatrix_apply] using coordinate_analyticAt b A z hA (σ i) i
  simpa only [LinearMap.det_toMatrix, determinant] using hm

theorem isUnit_iff_determinant_ne_zero (A : V →L[ℂ] V) :
    IsUnit A ↔ determinant A ≠ 0 := by
  classical
  let b := Module.finBasis ℂ V
  calc
    IsUnit A ↔ IsUnit A.toLinearMap := by
      change IsUnit ((Module.End.toContinuousLinearMap V) A.toLinearMap) ↔ _
      exact MulEquiv.isUnit_map (Module.End.toContinuousLinearMap V)
    _ ↔ IsUnit (LinearMap.toMatrix b b A.toLinearMap) :=
      (MulEquiv.isUnit_map (LinearMap.toMatrixAlgEquiv b)).symm
    _ ↔ IsUnit (LinearMap.toMatrix b b A.toLinearMap).det := Matrix.isUnit_iff_isUnit_det _
    _ ↔ determinant A ≠ 0 := by rw [LinearMap.det_toMatrix, isUnit_iff_ne_zero]; rfl

end OQ14.FiniteDimensionalDeterminant

#print axioms OQ14.FiniteDimensionalDeterminant.coordinate_analyticAt
#print axioms OQ14.FiniteDimensionalDeterminant.determinant_analyticAt
#print axioms OQ14.FiniteDimensionalDeterminant.isUnit_iff_determinant_ne_zero
