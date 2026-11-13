import Packet05GraphMetricUpper
import Mathlib.Data.Matrix.Notation

/-! Exact Jacobian and pullback metric algebra for the graph chart
(y₀,y₁,y₂) ↦ (y₀,y₁,y₂+γ(y₀,y₁)). -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace OQ14.Packet05GraphChartMatrix
open Matrix

def jacobian (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,1,0; a,b,1]
def inverseJacobian (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 0,1,0; -a,-b,1]
def metric (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,-a; 0,1,-b; -a,-b,1+a^2+b^2]

theorem inverse_jacobian_left (a b : ℝ) : inverseJacobian a b * jacobian a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_three]

theorem inverse_jacobian_right (a b : ℝ) : jacobian a b * inverseJacobian a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_three]

theorem metric_eq_pullback (a b : ℝ) :
    inverseJacobian a b * (inverseJacobian a b)ᵀ = metric a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, inverseJacobian, Matrix.mul_apply, Fin.sum_univ_three]
  <;> ring

theorem jacobian_determinant (a b : ℝ) : (jacobian a b).det = 1 := by
  simp [jacobian, Matrix.det_fin_three]

end OQ14.Packet05GraphChartMatrix
#print axioms OQ14.Packet05GraphChartMatrix.inverse_jacobian_left
#print axioms OQ14.Packet05GraphChartMatrix.inverse_jacobian_right
#print axioms OQ14.Packet05GraphChartMatrix.metric_eq_pullback
#print axioms OQ14.Packet05GraphChartMatrix.jacobian_determinant
