import AngularHarmonicEnergy

/-! Literal vector polynomial differential identities in three dimensions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PolynomialVectorCalculus
open MvPolynomial OQ14.HarmonicPolynomial
open OQ14.AngularHarmonicEnergy (partial_commute)

abbrev Vec := Fin 3 → Poly
def grad (p : Poly) : Vec := fun i => pderiv i p
def div (Q : Vec) : Poly := ∑ i : Fin 3,pderiv i (Q i)
def curl (Q : Vec) : Vec :=
  ![pderiv 1 (Q 2)-pderiv 2 (Q 1),pderiv 2 (Q 0)-pderiv 0 (Q 2),pderiv 0 (Q 1)-pderiv 1 (Q 0)]
def radialDot (Q : Vec) : Poly := ∑ i : Fin 3,X i*Q i
def radial (p : Poly) : Vec := fun i => X i*p
def tor (Q : Vec) : Vec := ![Q 1*X 2-Q 2*X 1,Q 2*X 0-Q 0*X 2,Q 0*X 1-Q 1*X 0]

theorem tor_grad (p : Poly) : tor (grad p)=AngularHarmonicEnergy.toroidal p := rfl

theorem radialDot_tor (Q : Vec) : radialDot (tor Q)=0 := by
  simp [radialDot,tor,Fin.sum_univ_three]
  ring

theorem tor_tor (Q : Vec) (i : Fin 3) :
    tor (tor Q) i=X i*radialDot Q-radiusSq*Q i := by
  fin_cases i <;> simp [tor,radialDot,radiusSq,Fin.sum_univ_three] <;> ring

theorem grad_radialDot (Q : Vec) (a : ℝ)
    (he : ∀ i : Fin 3,(∑ j : Fin 3,X j*pderiv j (Q i))=C a*Q i) (i : Fin 3) :
    grad (radialDot Q) i=C (a+1)*Q i-tor (curl Q) i := by
  have hi := he i
  fin_cases i <;> simp [grad,radialDot,tor,curl,Fin.sum_univ_three,pderiv_mul,pderiv_X] at hi ⊢ <;>
    linear_combination hi

theorem curl_curl (Q : Vec) (i : Fin 3) :
    curl (curl Q) i=grad (div Q) i-formalLaplacian (Q i) := by
  fin_cases i
  · simp [curl,grad,div,formalLaplacian_apply,Fin.sum_univ_three,partial_commute]
    ring
  · simp [curl,grad,div,formalLaplacian_apply,Fin.sum_univ_three,partial_commute]
    rw [partial_commute (Q 0) 0 1]
    ring
  · simp [curl,grad,div,formalLaplacian_apply,Fin.sum_univ_three,partial_commute]
    ring

theorem div_curl (Q : Vec) : div (curl Q)=0 := by
  simp [div,curl,Fin.sum_univ_three,partial_commute]

theorem laplacian_pderiv (p : Poly) (i : Fin 3) :
    formalLaplacian (pderiv i p)=pderiv i (formalLaplacian p) := by
  simp [formalLaplacian_apply,Fin.sum_univ_three,partial_commute]


theorem laplacian_radialDot (Q : Vec) :
    formalLaplacian (radialDot Q)=2*div Q+radialDot (fun i => formalLaplacian (Q i)) := by
  simp [radialDot,div,formalLaplacian_apply,Fin.sum_univ_three,pderiv_mul,pderiv_X]
  ring

theorem laplacian_curl (Q : Vec) (i : Fin 3) :
    formalLaplacian (curl Q i)=curl (fun j => formalLaplacian (Q j)) i := by
  fin_cases i <;> simp [curl,laplacian_pderiv]

theorem laplacian_div (Q : Vec) :
    formalLaplacian (div Q)=div (fun i => formalLaplacian (Q i)) := by
  simp [div,laplacian_pderiv,map_sum]


theorem tor_sub (Q V : Vec) (i : Fin 3) : tor (fun j => Q j-V j) i=tor Q i-tor V i := by
  fin_cases i <;> simp [tor] <;> ring

theorem tor_Cmul (a : ℝ) (Q : Vec) (i : Fin 3) : tor (fun j => C a*Q j) i=C a*tor Q i := by
  fin_cases i <;> simp [tor] <;> ring

end OQ14.PolynomialVectorCalculus

#print axioms OQ14.PolynomialVectorCalculus.tor_grad

#print axioms OQ14.PolynomialVectorCalculus.radialDot_tor

#print axioms OQ14.PolynomialVectorCalculus.tor_tor

#print axioms OQ14.PolynomialVectorCalculus.grad_radialDot

#print axioms OQ14.PolynomialVectorCalculus.curl_curl

#print axioms OQ14.PolynomialVectorCalculus.div_curl

#print axioms OQ14.PolynomialVectorCalculus.laplacian_pderiv

#print axioms OQ14.PolynomialVectorCalculus.laplacian_radialDot

#print axioms OQ14.PolynomialVectorCalculus.laplacian_curl

#print axioms OQ14.PolynomialVectorCalculus.laplacian_div

#print axioms OQ14.PolynomialVectorCalculus.tor_sub

#print axioms OQ14.PolynomialVectorCalculus.tor_Cmul
