import Packet05GraphH2Pullback

/-! Bounded C² coefficients preserve all actual H² weak partials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05BoundedMultiplierH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05BoundedWeakMultiplier
  OQ14.Packet05LocalizedAnisotropic

theorem bounded_multiplier_h2 (a : Space → ℂ) (ha : ContDiff ℝ 2 a)
    (hbound : MemLp a ⊤ volume)
    (hdi : ∀ i, MemLp (fun x => dcoord a x i) ⊤ volume)
    (hdd : ∀ i j, MemLp (fun x => dcoord (fun y => dcoord a y i) x j) ⊤ volume)
    (u : L2Scalar) (G : L2Vector) (H : Fin 3 → L2Vector)
    (hG : ∀ i, HasWeakPartial u (G i) i)
    (hH : ∀ i j, HasWeakPartial (G i) (H i j) j) :
    ∃ D : L2Vector, ∃ K : Fin 3 → L2Vector,
      (∀ i, HasWeakPartial (boundedMultiply a hbound u) (D i) i) ∧
      (∀ i j, HasWeakPartial (D i) (K i j) j) := by
  let D (i : Fin 3) := boundedMultiply a hbound (G i) +
    boundedMultiply (fun x => dcoord a x i) (hdi i) u
  have hD (i : Fin 3) : HasWeakPartial (boundedMultiply a hbound u) (D i) i :=
    bounded_multiplier_weak_partial a (ha.of_le (by norm_num)) hbound i (hdi i) u (G i) (hG i)
  have hsecond (i j : Fin 3) : ∃ v, HasWeakPartial (D i) v j := by
    have hai : ContDiff ℝ 1 (fun x => dcoord a x i) := KernelSource.partial_contDiff ha i
    have h1 := bounded_multiplier_weak_partial a (ha.of_le (by norm_num)) hbound j (hdi j)
      (G i) (H i j) (hH i j)
    have h2 := bounded_multiplier_weak_partial (fun x => dcoord a x i) hai (hdi i) j (hdd i j)
      u (G j) (hG j)
    exact ⟨_, weak_partial_add _ _ _ _ j h1 h2⟩
  classical
  let K (i j : Fin 3) := Classical.choose (hsecond i j)
  exact ⟨D, K, hD, fun i j => Classical.choose_spec (hsecond i j)⟩

end OQ14.Packet05BoundedMultiplierH2
#print axioms OQ14.Packet05BoundedMultiplierH2.bounded_multiplier_h2
