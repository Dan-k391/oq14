import Packet05ChartLinearEquiv
import Packet05RegionalDivergence

/-! Tests transported through signed Cartesian chart coordinates retain
compact support and acquire the exact signed directional derivative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartTestTransport
open OQ14.Maxwell OQ14.WeakCurl OQ14.Packet05ChartOrientation
  OQ14.Packet05ChartOrientationMeasure OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv

def forwardTest (up : Bool) (i : Fin 3) (φ : Test) : Test where
  function := φ.function ∘ orientedLinear up i
  regular := φ.regular.comp (orientedLinear up i).toContinuousLinearMap.contDiff
  compact := φ.compact.comp_homeomorph (orientedHomeomorph up i)

theorem forward_test_partial (up : Bool) (i j : Fin 3) (φ : Test) (x : Maxwell.Space) :
    dcoord (forwardTest up i φ).function x (Equiv.swap i 2 j) =
      (chartSign up j : ℂ) * dcoord φ.function (orientedLinear up i x) j := by
  change fderiv ℝ (φ.function ∘ (orientedLinear up i).toContinuousLinearMap) x
    (basis (Equiv.swap i 2 j)) = _
  rw [fderiv_comp x (φ.regular.differentiable (by norm_num) _)
    (orientedLinear up i).toContinuousLinearMap.differentiableAt,
    (orientedLinear up i).toContinuousLinearMap.fderiv]
  change (fderiv ℝ φ.function (orientedLinear up i x))
    (orientedLinear up i (basis (Equiv.swap i 2 j))) = _
  rw [oriented_forward_basis]
  simp [dcoord,Complex.real_smul]

end OQ14.Packet05ChartTestTransport
#print axioms OQ14.Packet05ChartTestTransport.forward_test_partial
