import CompactEntireLift
import ModalOrigin
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Uniform-norm analyticity of the actual regular dipole on the material core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalCoreAnalytic

open Complex Metric OQ14.Maxwell OQ14.ModalOrigin OQ14.ModalDipole
open scoped Topology

abbrev Core := closedBall (0 : Space) 1
instance : CompactSpace Core := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
abbrev ScalarContinuous := C(Core, ℂ)

def radius : ScalarContinuous :=
  ⟨fun x => (‖(x : Space)‖ : ℂ),
    continuous_ofReal.comp continuous_subtype_val.norm⟩

def position (j : Fin 3) : ScalarContinuous :=
  ⟨fun x => ((x : Space) j : ℂ),
    (OQ14.Maxwell.coordinate j).continuous.comp continuous_subtype_val⟩

def profileCore : ℂ → ScalarContinuous :=
  CompactEntireLift.lift radius profile profile_differentiable.continuous

def derivativeCore : ℂ → ScalarContinuous :=
  CompactEntireLift.lift radius (deriv profile) profile_deriv_differentiable.continuous

def slopeCore : ℂ → ScalarContinuous :=
  CompactEntireLift.lift radius profileSlope profileSlope_differentiable.continuous

theorem profileCore_analytic (k : ℂ) : AnalyticAt ℂ profileCore k :=
  CompactEntireLift.analyticAt_lift radius profile profile_differentiable k

theorem derivativeCore_analytic (k : ℂ) : AnalyticAt ℂ derivativeCore k :=
  CompactEntireLift.analyticAt_lift radius (deriv profile) profile_deriv_differentiable k

theorem slopeCore_analytic (k : ℂ) : AnalyticAt ℂ slopeCore k :=
  CompactEntireLift.analyticAt_lift radius profileSlope profileSlope_differentiable k

def radialA (k : ℂ) : ScalarContinuous :=
  k^2 • ((2 : ℂ) • profileCore k + (k • radius) * derivativeCore k)

def radialB (k : ℂ) : ScalarContinuous := -k^4 • slopeCore k

theorem radialA_analytic (k : ℂ) : AnalyticAt ℂ radialA k := by
  exact (analyticAt_id.pow 2).smul
    (((profileCore_analytic k).fun_const_smul (c := (2 : ℂ))).add
      ((analyticAt_id.smul analyticAt_const).mul (derivativeCore_analytic k)))

theorem radialB_analytic (k : ℂ) : AnalyticAt ℂ radialB k := by
  exact (analyticAt_id.pow 4).neg.smul (slopeCore_analytic k)

theorem radialA_actual (k : ℂ) (x : Core) : radialA k x = centerA k ‖(x : Space)‖ := rfl
theorem radialB_actual (k : ℂ) (x : Core) : radialB k x = centerB k ‖(x : Space)‖ := rfl

def electric (k : ℂ) : Fin 3 → ScalarContinuous :=
  ![radialB k * position 2 * position 0,
    radialB k * position 2 * position 1,
    radialA k + radialB k * position 2 * position 2]

theorem electric_analytic (j : Fin 3) (k : ℂ) :
    AnalyticAt ℂ (fun z => electric z j) k := by
  have hB (i j : Fin 3) : AnalyticAt ℂ (fun z => radialB z * position i * position j) k :=
    ((radialB_analytic k).mul analyticAt_const).mul analyticAt_const
  fin_cases j
  · simpa [electric] using hB 2 0
  · simpa [electric] using hB 2 1
  · simpa [electric] using (radialA_analytic k).add (hB 2 2)

theorem electric_actual (k : ℂ) (x : Core) (j : Fin 3) :
    electric k j x = centerE k x.val j := by
  fin_cases j <;>
    simp [electric, radialA_actual, radialB_actual, position, centerE, axisField]

def numerator (n k : ℂ) : Fin 3 → ScalarContinuous :=
  fun j => (I/n) • electric (n*k) j

theorem numerator_analytic (n : ℂ) (j : Fin 3) (k : ℂ) :
    AnalyticAt ℂ (fun z => numerator n z j) k :=
  ((electric_analytic j (n*k)).comp (analyticAt_const.mul analyticAt_id)).fun_const_smul

theorem numerator_actual (n k : ℂ) (x : Core) (j : Fin 3) :
    numerator n k j x = (I/n)*centerE (n*k) x.val j := by
  simp only [numerator, ContinuousMap.smul_apply, smul_eq_mul, electric_actual]

end OQ14.ModalCoreAnalytic

#print axioms OQ14.ModalCoreAnalytic.profileCore_analytic
#print axioms OQ14.ModalCoreAnalytic.derivativeCore_analytic
#print axioms OQ14.ModalCoreAnalytic.slopeCore_analytic
#print axioms OQ14.ModalCoreAnalytic.radialA_analytic
#print axioms OQ14.ModalCoreAnalytic.radialB_analytic
#print axioms OQ14.ModalCoreAnalytic.radialA_actual
#print axioms OQ14.ModalCoreAnalytic.radialB_actual
#print axioms OQ14.ModalCoreAnalytic.electric_analytic
#print axioms OQ14.ModalCoreAnalytic.electric_actual
#print axioms OQ14.ModalCoreAnalytic.numerator_analytic
#print axioms OQ14.ModalCoreAnalytic.numerator_actual
