import AngularPolynomialMean

/-! Actual angular derivative energies of homogeneous harmonic polynomials. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000

namespace OQ14.AngularHarmonicEnergy

open MeasureTheory Set MvPolynomial OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.SphereHarmonicOrthogonality OQ14.AngularPolynomialMean

def gradientDot (p q : Poly) : Poly := ∑ i : Fin 3,pderiv i p*pderiv i q

def tangential (p : Poly) (l : ℕ) (i : Fin 3) : Poly :=
  pderiv i p-(l : ℝ) • (X i*p)

def toroidal (p : Poly) : Fin 3 → Poly :=
  ![pderiv 1 p*X 2-pderiv 2 p*X 1,
    pderiv 2 p*X 0-pderiv 0 p*X 2,
    pderiv 0 p*X 1-pderiv 1 p*X 0]

def polynomialDot (v w : Fin 3 → Poly) : Poly := ∑ i : Fin 3,v i*w i

theorem laplacian_product (p q : Poly) :
    formalLaplacian (p*q)=formalLaplacian p*q+(2 : ℝ) • gradientDot p q+
      p*formalLaplacian q := by
  simp only [formalLaplacian_apply,gradientDot,Fin.sum_univ_three,pderiv_mul,
    map_add,smul_eq_C_mul,map_ofNat]
  ring

theorem gradient_mean (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) :
    2*mean (gradientDot p q)=(l+m : ℝ)*(l+m+1)*mean (p*q) := by
  have h := mean_laplacian (p*q) (l+m) (hp.mul hq)
  rw [laplacian_product,hpH,hqH,zero_mul,mul_zero,zero_add,add_zero,map_smul] at h
  simpa only [smul_eq_mul,Nat.cast_add] using h

theorem euler (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    (∑ i : Fin 3,X i*pderiv i p)=(l : ℝ) • p := by
  simpa only [nsmul_eq_mul,smul_eq_C_mul,map_natCast] using hp.sum_X_mul_pderiv

theorem tangential_dot (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m) :
    polynomialDot (tangential p l) (tangential q m)=
      gradientDot p q-(2*(l : ℝ)*m) • (p*q)+((l : ℝ)*m) • (radiusSq*(p*q)) := by
  have he := euler p l hp
  have hf := euler q m hq
  simp only [polynomialDot,tangential,gradientDot,radiusSq,Fin.sum_univ_three,
    smul_eq_C_mul,map_mul,map_ofNat] at he hf ⊢
  linear_combination -(C (m : ℝ)*q)*he-(C (l : ℝ)*p)*hf

theorem tangential_mean (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m) :
    mean (polynomialDot (tangential p l) (tangential q m))=
      mean (gradientDot p q)-(l : ℝ)*m*mean (p*q) := by
  rw [tangential_dot p q l m hp hq,map_add,map_sub,map_smul,map_smul]
  rw [show radiusSq*(p*q)=radiusSq^1*(p*q) by simp,mean_radiusSq_pow]
  simp only [smul_eq_mul]
  ring

theorem toroidal_dot (p q : Poly) :
    polynomialDot (toroidal p) (toroidal q)=radiusSq*gradientDot p q-
      (∑ i : Fin 3,X i*pderiv i p)*(∑ i : Fin 3,X i*pderiv i q) := by
  simp [polynomialDot,toroidal,radiusSq,gradientDot,Fin.sum_univ_three]
  ring

theorem toroidal_mean (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m) :
    mean (polynomialDot (toroidal p) (toroidal q))=
      mean (gradientDot p q)-(l : ℝ)*m*mean (p*q) := by
  rw [toroidal_dot,euler p l hp,euler q m hq]
  rw [show ((l : ℝ) • p)*((m : ℝ) • q)=((l : ℝ)*m) • (p*q) by
    simp only [smul_eq_C_mul,map_mul]; ring]
  rw [map_sub,map_smul,show radiusSq*gradientDot p q=radiusSq^1*gradientDot p q by simp,
    mean_radiusSq_pow]
  simp only [smul_eq_mul]

theorem harmonic_product_mean_zero (p q : Poly) (l m : ℕ)
    (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) (hlm : l ≠ m) : mean (p*q)=0 := by
  change (∫ n : Sphere,SpherePolynomial.polynomialMap (p*q) n ∂angularMeasure)=0
  simpa only [map_mul,ContinuousMap.mul_apply] using harmonic_integral_zero p q l m hp hq hpH hqH hlm

theorem tangential_energy (p q : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous l)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) :
    mean (polynomialDot (tangential p l) (tangential q l))=
      (l : ℝ)*(l+1)*mean (p*q) := by
  rw [tangential_mean p q l l hp hq]
  have h := gradient_mean p q l l hp hq hpH hqH
  nlinarith

theorem toroidal_energy (p q : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous l)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) :
    mean (polynomialDot (toroidal p) (toroidal q))=(l : ℝ)*(l+1)*mean (p*q) := by
  rw [toroidal_mean p q l l hp hq]
  have h := gradient_mean p q l l hp hq hpH hqH
  nlinarith

theorem tangential_cross_degree (p q : Poly) (l m : ℕ)
    (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) (hlm : l ≠ m) :
    mean (polynomialDot (tangential p l) (tangential q m))=0 := by
  rw [tangential_mean p q l m hp hq,harmonic_product_mean_zero p q l m hp hq hpH hqH hlm,mul_zero,sub_zero]
  have h := gradient_mean p q l m hp hq hpH hqH
  rw [harmonic_product_mean_zero p q l m hp hq hpH hqH hlm,mul_zero] at h
  linarith

theorem toroidal_cross_degree (p q : Poly) (l m : ℕ)
    (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m)
    (hpH : formalLaplacian p=0) (hqH : formalLaplacian q=0) (hlm : l ≠ m) :
    mean (polynomialDot (toroidal p) (toroidal q))=0 := by
  rw [toroidal_mean p q l m hp hq,harmonic_product_mean_zero p q l m hp hq hpH hqH hlm,mul_zero,sub_zero]
  have h := gradient_mean p q l m hp hq hpH hqH
  rw [harmonic_product_mean_zero p q l m hp hq hpH hqH hlm,mul_zero] at h
  linarith

theorem partial_commute (p : Poly) (i j : Fin 3) :
    pderiv i (pderiv j p)=pderiv j (pderiv i p) := by
  by_cases hij : i=j
  · subst j
    rfl
  · induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p k ih =>
        by_cases hi : k=i <;> by_cases hj : k=j <;>
          simp [pderiv_mul,pderiv_X,Pi.single_apply,hi,hj,hij,Ne.symm hij,eq_comm,ih] <;> ring

theorem toroidal_radial_zero (p : Poly) : (∑ i : Fin 3,X i*toroidal p i)=0 := by
  simp [toroidal,Fin.sum_univ_three]
  ring

theorem toroidal_divergence_zero (p : Poly) : (∑ i : Fin 3,pderiv i (toroidal p i))=0 := by
  simp [toroidal,Fin.sum_univ_three,pderiv_mul]
  rw [partial_commute p 0 1,partial_commute p 0 2,partial_commute p 1 2]
  ring

theorem partial_X_homogeneous (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (i j : Fin 3) :
    (pderiv i p*X j).IsHomogeneous l := by
  cases l with
  | zero =>
      have hc := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
      rw [hc,pderiv_C,zero_mul]
      exact isHomogeneous_zero (Fin 3) ℝ 0
  | succ l =>
      simpa only [Nat.succ_sub_one] using (hp.pderiv (i := i)).mul (isHomogeneous_X ℝ j)

theorem toroidal_homogeneous (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (i : Fin 3) :
    (toroidal p i).IsHomogeneous l := by
  fin_cases i <;> dsimp [toroidal]
  · exact (homogeneousSubmodule (Fin 3) ℝ l).sub_mem
      (partial_X_homogeneous p l hp 1 2) (partial_X_homogeneous p l hp 2 1)
  · exact (homogeneousSubmodule (Fin 3) ℝ l).sub_mem
      (partial_X_homogeneous p l hp 2 0) (partial_X_homogeneous p l hp 0 2)
  · exact (homogeneousSubmodule (Fin 3) ℝ l).sub_mem
      (partial_X_homogeneous p l hp 0 1) (partial_X_homogeneous p l hp 1 0)

theorem mean_divergence_zero (v : Fin 3 → Poly) (d : ℕ)
    (hv : ∀ i,(v i).IsHomogeneous d) (hr : (∑ i : Fin 3,X i*v i)=0) :
    mean (∑ i : Fin 3,pderiv i (v i))=0 := by
  rw [map_sum]
  simp_rw [mean_partial _ d (hv _) _]
  rw [← Finset.mul_sum,← map_sum,hr,map_zero,mul_zero]

theorem toroidal_tangential_dot (p q : Poly) (m : ℕ) :
    polynomialDot (toroidal p) (tangential q m)=∑ i : Fin 3,pderiv i (q*toroidal p i) := by
  have hr := toroidal_radial_zero p
  have hd := toroidal_divergence_zero p
  simp only [polynomialDot,tangential,Fin.sum_univ_three,pderiv_mul,
    smul_eq_C_mul] at hr hd ⊢
  linear_combination -(C (m : ℝ)*q)*hr-q*hd

theorem mixed_mean_zero (p q : Poly) (l m : ℕ) (hp : p.IsHomogeneous l) (hq : q.IsHomogeneous m) :
    mean (polynomialDot (toroidal p) (tangential q m))=0 := by
  rw [toroidal_tangential_dot]
  apply mean_divergence_zero (fun i => q*toroidal p i) (m+l)
  · intro i
    exact hq.mul (toroidal_homogeneous p l hp i)
  · have hr := toroidal_radial_zero p
    simp only [Fin.sum_univ_three] at hr ⊢
    linear_combination q*hr

end OQ14.AngularHarmonicEnergy

#print axioms OQ14.AngularHarmonicEnergy.laplacian_product
#print axioms OQ14.AngularHarmonicEnergy.gradient_mean
#print axioms OQ14.AngularHarmonicEnergy.euler
#print axioms OQ14.AngularHarmonicEnergy.tangential_dot
#print axioms OQ14.AngularHarmonicEnergy.tangential_mean
#print axioms OQ14.AngularHarmonicEnergy.toroidal_dot
#print axioms OQ14.AngularHarmonicEnergy.toroidal_mean
#print axioms OQ14.AngularHarmonicEnergy.harmonic_product_mean_zero
#print axioms OQ14.AngularHarmonicEnergy.tangential_energy
#print axioms OQ14.AngularHarmonicEnergy.toroidal_energy
#print axioms OQ14.AngularHarmonicEnergy.tangential_cross_degree
#print axioms OQ14.AngularHarmonicEnergy.toroidal_cross_degree
#print axioms OQ14.AngularHarmonicEnergy.partial_commute
#print axioms OQ14.AngularHarmonicEnergy.toroidal_radial_zero
#print axioms OQ14.AngularHarmonicEnergy.toroidal_divergence_zero
#print axioms OQ14.AngularHarmonicEnergy.partial_X_homogeneous
#print axioms OQ14.AngularHarmonicEnergy.toroidal_homogeneous
#print axioms OQ14.AngularHarmonicEnergy.mean_divergence_zero
#print axioms OQ14.AngularHarmonicEnergy.toroidal_tangential_dot
#print axioms OQ14.AngularHarmonicEnergy.mixed_mean_zero
