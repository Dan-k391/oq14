import SphereMeasure
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Actual real polynomial approximation on the Euclidean unit sphere -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OQ14.SpherePolynomial
open MeasureTheory Metric
abbrev Space := FourierL2.Space
abbrev Sphere := sphere (0 : Space) 1
abbrev Poly := MvPolynomial (Fin 3) ℝ

def coordinate (i : Fin 3) : C(Sphere, ℝ) where
  toFun n := (n : Space) i
  continuous_toFun := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp continuous_subtype_val

def polynomialMap : Poly →ₐ[ℝ] C(Sphere, ℝ) := MvPolynomial.aeval coordinate

theorem polynomialMap_apply (p : Poly) (n : Sphere) :
    polynomialMap p n = MvPolynomial.eval (fun i => (n : Space) i) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [polynomialMap]
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
  | mul_X p i hp => simp [polynomialMap, map_mul, ← hp, coordinate]

def polynomialAlgebra : Subalgebra ℝ C(Sphere, ℝ) := polynomialMap.range

theorem polynomialAlgebra_separatesPoints : polynomialAlgebra.SeparatesPoints := by
  intro x y hxy
  have hval : (x : Space) ≠ (y : Space) := fun h => hxy (Subtype.ext h)
  have hi : ∃ i : Fin 3, (x : Space) i ≠ (y : Space) i := by
    by_contra h
    push_neg at h
    exact hval (PiLp.ext h)
  obtain ⟨i, hi⟩ := hi
  refine ⟨coordinate i, ⟨coordinate i, ?_, rfl⟩, hi⟩
  exact ⟨MvPolynomial.X i, by simp [polynomialMap]⟩

theorem polynomialAlgebra_closure_top : polynomialAlgebra.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    polynomialAlgebra polynomialAlgebra_separatesPoints

theorem polynomialMap_denseRange : DenseRange polynomialMap := by
  change Dense (polynomialAlgebra : Set C(Sphere, ℝ))
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, polynomialAlgebra_closure_top]
  rfl

theorem exists_polynomial_uniform_approximation (f : C(Sphere, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Poly, ‖polynomialMap p - f‖ < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    polynomialAlgebra polynomialAlgebra_separatesPoints f ε hε
  obtain ⟨p, hp⟩ := (show ∃ p : Poly, polynomialMap p = (g : C(Sphere, ℝ)) from g.property)
  refine ⟨p, ?_⟩
  rw [hp]
  exact hg

end OQ14.SpherePolynomial


#print axioms OQ14.SpherePolynomial.polynomialMap_apply
#print axioms OQ14.SpherePolynomial.polynomialAlgebra_separatesPoints
#print axioms OQ14.SpherePolynomial.polynomialAlgebra_closure_top
#print axioms OQ14.SpherePolynomial.polynomialMap_denseRange
#print axioms OQ14.SpherePolynomial.exists_polynomial_uniform_approximation
