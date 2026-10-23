import HarmonicVectorDecomposition

/-! The degree-zero vector sector, without division by its degree. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.HarmonicVectorConstants
open MvPolynomial OQ14.HarmonicPolynomial OQ14.PolynomialVectorCalculus

theorem partial_zero (p : Poly) (hp : p.IsHomogeneous 0) (i : Fin 3) : pderiv i p=0 := by
  have he := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
  rw [he,pderiv_C]

theorem div_zero (Q : Vec) (hp : ∀ i,(Q i).IsHomogeneous 0) : div Q=0 := by
  simp only [div,partial_zero _ (hp _),Finset.sum_const_zero]

theorem curl_zero (Q : Vec) (hp : ∀ i,(Q i).IsHomogeneous 0) : curl Q=0 := by
  funext i
  fin_cases i <;> simp [curl,partial_zero _ (hp _)]

theorem decomposition (Q : Vec) (hp : ∀ i,(Q i).IsHomogeneous 0) :
    grad (radialDot Q)=Q := by
  funext i
  have h := grad_radialDot Q 0 (by intro j; simp [partial_zero _ (hp j)]) i
  fin_cases i <;> simpa [curl_zero Q hp,tor] using h

theorem radialDot_harmonic (Q : Vec) (hp : ∀ i,(Q i).IsHomogeneous 0) :
    formalLaplacian (radialDot Q)=0 := by
  rw [laplacian_radialDot,div_zero Q hp]
  simp [radialDot,formalLaplacian_apply,partial_zero _ (hp _)]

end OQ14.HarmonicVectorConstants

#print axioms OQ14.HarmonicVectorConstants.partial_zero
#print axioms OQ14.HarmonicVectorConstants.div_zero
#print axioms OQ14.HarmonicVectorConstants.curl_zero
#print axioms OQ14.HarmonicVectorConstants.decomposition
#print axioms OQ14.HarmonicVectorConstants.radialDot_harmonic
