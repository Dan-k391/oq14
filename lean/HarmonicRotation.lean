import HarmonicPolynomial
import SphereAngularSymmetry

/-! Actual orthogonal substitution on homogeneous harmonic polynomials. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.HarmonicRotation

open MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial
open scoped RealInnerProductSpace

def entry (L : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) : ℝ := (L (basis j)) i

def coordinatePolynomial (L : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3) : Poly :=
  ∑ j : Fin 3, C (entry L i j)*X j

def rotate (L : Space ≃ₗᵢ[ℝ] Space) : Poly →ₐ[ℝ] Poly :=
  MvPolynomial.aeval (coordinatePolynomial L)

theorem coordinatePolynomial_homogeneous (L : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3) :
    (coordinatePolynomial L i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℝ j).C_mul _)

theorem rotate_homogeneous (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) : (rotate L p).IsHomogeneous l := by
  simpa only [one_mul] using hp.aeval (coordinatePolynomial L) (coordinatePolynomial_homogeneous L)

theorem rotate_X (L : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3) : rotate L (X i)=coordinatePolynomial L i :=
  aeval_X _ _

theorem coordinatePolynomial_pderiv (L : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) :
    pderiv j (coordinatePolynomial L i)=C (entry L i j) := by
  fin_cases i <;> fin_cases j <;> simp [coordinatePolynomial,Fin.sum_univ_three,pderiv_mul]

theorem coordinatePolynomial_evaluate (L : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3) (x : Space) :
    evaluate (coordinatePolynomial L i) x=(L x) i := by
  have hx : x=∑ j : Fin 3, (x j) • basis j := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_three,basis,EuclideanSpace.single_apply]
  calc
    _ = ∑ j : Fin 3, entry L i j*x j := by simp [evaluate,coordinatePolynomial]
    _ = (L (∑ j : Fin 3, (x j) • basis j)) i := by
      simp [entry,map_sum,map_smul,mul_comm,Fin.sum_univ_three,PiLp.add_apply,PiLp.smul_apply]
    _ = (L x) i := by rw [← hx]

theorem rotate_evaluate (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) (x : Space) :
    evaluate (rotate L p) x=evaluate p (L x) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evaluate,rotate]
  | add p q hp hq => simpa only [map_add,evaluate] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    simp only [map_mul,rotate_X,evaluate,MvPolynomial.eval_mul,MvPolynomial.eval_X]
    rw [show MvPolynomial.eval (fun i => x i) (coordinatePolynomial L i)=(L x) i from
      coordinatePolynomial_evaluate L i x]
    exact congrArg (·*(L x) i) hp

theorem entry_transpose (L : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) :
    entry L i j=entry L.symm j i := by
  have h := L.inner_map_map (L.symm (basis i)) (basis j)
  simpa only [L.apply_symm_apply,basis,EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,mul_one,entry] using h

theorem entry_row_orthogonal (L : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) :
    (∑ a : Fin 3, entry L i a*entry L j a)=if i=j then 1 else 0 := by
  simp_rw [entry_transpose L]
  calc
    _ = ⟪L.symm (basis j),L.symm (basis i)⟫ := rfl
    _ = ⟪basis j,basis i⟫ := L.symm.inner_map_map _ _
    _ = if i=j then 1 else 0 := by
      simp [basis,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply,eq_comm]

theorem pderiv_rotate (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) (j : Fin 3) :
    pderiv j (rotate L p)=∑ i : Fin 3, C (entry L i j)*rotate L (pderiv i p) := by
  induction p using MvPolynomial.induction_on generalizing j with
  | C a => simp [rotate,pderiv_C]
  | add p q hp hq =>
    simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,rotate_X,coordinatePolynomial_pderiv]
    rw [hp]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three,pderiv_X,map_add,map_mul,rotate_X] <;> ring

theorem polynomial_row_orthogonal (L : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) :
    (∑ a : Fin 3, C (entry L i a)*C (entry L j a) : Poly)=if i=j then 1 else 0 := by
  simp_rw [← map_mul]
  rw [← map_sum,entry_row_orthogonal]
  split_ifs <;> simp

theorem second_rotate (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) (a : Fin 3) :
    pderiv a (pderiv a (rotate L p))=∑ i : Fin 3, ∑ j : Fin 3,
      C (entry L i a)*C (entry L j a)*rotate L (pderiv j (pderiv i p)) := by
  rw [pderiv_rotate,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_mul,pderiv_C,zero_mul,zero_add,pderiv_rotate,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem laplacian_rotate (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) :
    formalLaplacian (rotate L p)=rotate L (formalLaplacian p) := by
  rw [formalLaplacian_apply]
  simp_rw [second_rotate]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (∑ a : Fin 3, C (entry L i a)*C (entry L j a))*
        rotate L (pderiv j (pderiv i p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i : Fin 3, rotate L (pderiv i (pderiv i p)) := by
      simp_rw [polynomial_row_orthogonal]
      simp only [ite_mul,one_mul,zero_mul]
      simp
    _ = rotate L (formalLaplacian p) := by rw [formalLaplacian_apply,map_sum]

theorem rotate_harmonic (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) (hp : formalLaplacian p=0) :
    formalLaplacian (rotate L p)=0 := by rw [laplacian_rotate,hp,map_zero]

theorem rotate_restriction (L : Space ≃ₗᵢ[ℝ] Space) (p : Poly) :
    SpherePolynomial.polynomialMap (rotate L p)=
      (SpherePolynomial.polynomialMap p).comp
        ⟨SphereAngularSymmetry.sphereMap L,(SphereAngularSymmetry.sphereMap L).continuous⟩ := by
  ext n
  simp only [SpherePolynomial.polynomialMap_apply,ContinuousMap.comp_apply]
  exact rotate_evaluate L p n

end OQ14.HarmonicRotation

#print axioms OQ14.HarmonicRotation.coordinatePolynomial_homogeneous
#print axioms OQ14.HarmonicRotation.rotate_homogeneous
#print axioms OQ14.HarmonicRotation.rotate_X
#print axioms OQ14.HarmonicRotation.coordinatePolynomial_pderiv
#print axioms OQ14.HarmonicRotation.coordinatePolynomial_evaluate
#print axioms OQ14.HarmonicRotation.rotate_evaluate
#print axioms OQ14.HarmonicRotation.entry_transpose
#print axioms OQ14.HarmonicRotation.entry_row_orthogonal
#print axioms OQ14.HarmonicRotation.pderiv_rotate
#print axioms OQ14.HarmonicRotation.polynomial_row_orthogonal
#print axioms OQ14.HarmonicRotation.second_rotate
#print axioms OQ14.HarmonicRotation.laplacian_rotate
#print axioms OQ14.HarmonicRotation.rotate_harmonic
#print axioms OQ14.HarmonicRotation.rotate_restriction
