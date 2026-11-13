import Packet07SignedConnected

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PhysicalLobes
open Set
abbrev Plane := ConicalSmoothCapGraph.Plane
abbrev Space := Maxwell.Space

def unsplit (y : Plane × ℝ) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![y.1 0, y.1 1, y.2]

def unsplitLinear : (Plane × ℝ) →ₗ[ℝ] Space where
  toFun := unsplit
  map_add' x y := by ext i; fin_cases i <;> simp [unsplit]
  map_smul' c x := by ext i; fin_cases i <;> simp [unsplit]

theorem unsplit_continuous : Continuous unsplit := unsplitLinear.continuous_of_finiteDimensional

theorem split_unsplit (y : Plane × ℝ) : ConicalJunctionPhysical.split (unsplit y) = y := by
  rcases y with ⟨u,z⟩
  apply Prod.ext
  · ext i; fin_cases i <;> simp [ConicalJunctionPhysical.split, ConicalJunctionPhysical.horizontal, unsplit]
  · simp [ConicalJunctionPhysical.split, unsplit]

theorem unsplit_split (x : Space) : unsplit (ConicalJunctionPhysical.split x) = x := by
  ext i; fin_cases i <;> simp [unsplit, ConicalJunctionPhysical.split, ConicalJunctionPhysical.horizontal]

theorem physical_lobe_path_connected (n : ℕ) (m a : ℝ) (center : Space) (up : Bool)
    (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+2)*ConicalTipRounding.radius n < a/2)
    (hrad : (2*ConicalTipRounding.radius n)^2 < a^2/8)
    (heball : ConicalTipRounding.radius n < a^2/8)
    (hc : (2*m+1)*ConicalTipRounding.radius n < a/3)
    (hr : (2*ConicalTipRounding.radius n)^2 < a^2/9) :
    IsPathConnected {x : Space | x-center ∈ ConicalJunctionPhysical.inclusion n m a ∧
      if up then center 2 < x 2 else x 2 < center 2} := by
  let S : Set (Plane × ℝ) := ConicalSmoothJunction.inclusion n m a ∩
    {y | if up then 0 < y.2 else y.2 < 0}
  have hs : IsPathConnected S := by
    cases up
    · exact Packet07SignedConnected.negative_path_connected n m a hm ha hcap hrad heball hc hr
    · exact Packet07PositiveConnected.positive_path_connected n m a hm ha hcap hrad heball hc hr
  have hf : Continuous (fun y : Plane × ℝ => center + unsplit y) := continuous_const.add unsplit_continuous
  have him := hs.image hf
  have heq : (fun y : Plane × ℝ => center + unsplit y) '' S =
      {x : Space | x-center ∈ ConicalJunctionPhysical.inclusion n m a ∧
        if up then center 2 < x 2 else x 2 < center 2} := by
    ext x
    constructor
    · rintro ⟨y,⟨hy,hsign⟩,rfl⟩
      have hi : center + unsplit y - center ∈ ConicalJunctionPhysical.inclusion n m a := by
        change ConicalJunctionPhysical.split (center + unsplit y - center) ∈ ConicalSmoothJunction.inclusion n m a
        simpa [split_unsplit] using hy
      refine ⟨hi, ?_⟩
      have hcoord : unsplit y 2 = y.2 := by
        have h := congrArg Prod.snd (split_unsplit y)
        simpa [ConicalJunctionPhysical.split] using h
      cases up <;> simp_all [PiLp.add_apply]
    · rintro ⟨hi,hsign⟩
      refine ⟨ConicalJunctionPhysical.split (x-center), ⟨hi,?_⟩, ?_⟩
      · cases up <;> simp_all [ConicalJunctionPhysical.split, PiLp.sub_apply]
      · change center + unsplit (ConicalJunctionPhysical.split (x-center)) = x
        rw [unsplit_split]
        abel
  simpa only [heq] using him

end OQ14.Packet07PhysicalLobes
#print axioms OQ14.Packet07PhysicalLobes.unsplit_continuous
#print axioms OQ14.Packet07PhysicalLobes.split_unsplit
#print axioms OQ14.Packet07PhysicalLobes.unsplit_split
#print axioms OQ14.Packet07PhysicalLobes.physical_lobe_path_connected
