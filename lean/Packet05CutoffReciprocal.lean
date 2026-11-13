import Packet05ScalarNormalH2

/-! Construct a genuine smooth compact reciprocal on a region where a
smooth coefficient is nonzero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05CutoffReciprocal
open Set Filter OQ14.Maxwell OQ14.WeakCurl
open scoped Topology

def reciprocalFunction (κ A : Test) (x : Space) : ℂ := κ.function x * (A.function x)⁻¹

theorem reciprocalFunction_regular (κ A : Test)
    (hA : ∀ x ∈ tsupport κ.function, A.function x ≠ 0) :
    ContDiff ℝ 1 (reciprocalFunction κ A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport κ.function
  · exact κ.regular.contDiffAt.mul (A.regular.contDiffAt.inv (hA x hx))
  · apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Space => (0 : ℂ)) x).congr_of_eventuallyEq
    filter_upwards [not_mem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change κ.function y * (A.function y)⁻¹ = 0
    rw [show κ.function y = 0 from hy]
    simp

def reciprocalTest (κ A : Test) (hA : ∀ x ∈ tsupport κ.function, A.function x ≠ 0) : Test where
  function := reciprocalFunction κ A
  regular := reciprocalFunction_regular κ A hA
  compact := κ.compact.mul_right

theorem reciprocalTest_support (κ A : Test) (hA : ∀ x ∈ tsupport κ.function, A.function x ≠ 0) :
    tsupport (reciprocalTest κ A hA).function ⊆ tsupport κ.function := tsupport_mul_subset_left

theorem reciprocalTest_identity (κ A : Test) (hA : ∀ x ∈ tsupport κ.function, A.function x ≠ 0)
    (W : Set Space) (hκ : ∀ x ∈ W, κ.function x = 1)
    (hAW : ∀ x ∈ W, A.function x ≠ 0) :
    ∀ x ∈ W, (reciprocalTest κ A hA).function x * A.function x = 1 := by
  intro x hx
  simp [reciprocalTest, reciprocalFunction, hκ x hx, hAW x hx]

end OQ14.Packet05CutoffReciprocal
#print axioms OQ14.Packet05CutoffReciprocal.reciprocalFunction_regular
#print axioms OQ14.Packet05CutoffReciprocal.reciprocalTest_support
#print axioms OQ14.Packet05CutoffReciprocal.reciprocalTest_identity
