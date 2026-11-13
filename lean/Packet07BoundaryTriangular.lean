import Packet07BoundaryNormal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryTriangular
abbrev Plane := ConicalSmoothCapGraph.Plane
abbrev Point := Plane × ℝ

def triangular (D : Point →L[ℝ] ℝ) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.fst ℝ Plane ℝ).prod D

theorem triangular_bijective (D : Point →L[ℝ] ℝ) (hD : D (0,1) ≠ 0) :
    Function.Bijective (triangular D) := by
  constructor
  · intro ⟨u,z⟩ ⟨v,w⟩ h
    have hu : u = v := congrArg Prod.fst h
    subst v
    have hz : D (u,z) = D (u,w) := congrArg Prod.snd h
    have he : D (0,z-w) = 0 := by
      have hh := congrArg (fun t : ℝ => t) (map_sub D (u,z) (u,w))
      simp only [Prod.mk_sub_mk, sub_self, hz, sub_self] at hh
      exact hh
    have he' : (z-w) * D (0,1) = 0 := by
      have hv : (0,z-w) = (z-w) • ((0,1) : Point) := by ext <;> simp
      rw [hv, map_smul] at he
      simpa only [smul_eq_mul] using he
    have : z = w := sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hD)
    simp [this]
  · intro ⟨u,z⟩
    let w := (z-D (u,0)) / D (0,1)
    refine ⟨(u,w), ?_⟩
    apply Prod.ext
    · rfl
    · change D (u,w) = z
      have hv : (u,w) = (u,0) + w • ((0,1) : Point) := by ext <;> simp
      rw [hv, map_add, map_smul]
      simp only [smul_eq_mul]
      dsimp [w]
      field_simp

end OQ14.Packet07BoundaryTriangular
#print axioms OQ14.Packet07BoundaryTriangular.triangular_bijective
