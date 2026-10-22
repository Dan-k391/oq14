import SphereHarmonicOrthogonality

/-! Actual homogeneous polynomial mean identities on the genuine sphere. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.AngularPolynomialMean

open MeasureTheory Set MvPolynomial OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.SphereHarmonicOrthogonality
open OQ14.FischerDecomposition (fischerSpan radiusSq_on_sphere homogeneous_mem_fischerSpan)

theorem restriction_integrable (p : Poly) :
    Integrable (SpherePolynomial.polynomialMap p) angularMeasure :=
  (SpherePolynomial.polynomialMap p).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def mean : Poly →ₗ[ℝ] ℝ where
  toFun p := ∫ n : Sphere,SpherePolynomial.polynomialMap p n ∂angularMeasure
  map_add' p q := by
    simp only [map_add,ContinuousMap.add_apply]
    exact integral_add (restriction_integrable p) (restriction_integrable q)
  map_smul' a p := by
    simp only [map_smul,ContinuousMap.smul_apply]
    exact integral_smul a _

theorem mean_radiusSq_pow (p : Poly) (j : ℕ) : mean (radiusSq^j*p)=mean p := by
  change (∫ n : Sphere,SpherePolynomial.polynomialMap (radiusSq^j*p) n ∂angularMeasure)=_
  simp only [map_mul,map_pow,radiusSq_on_sphere,one_pow,one_mul]
  rfl

theorem mean_harmonic_zero (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (hl : l ≠ 0) : mean p=0 := by
  have h := harmonic_integral_zero p 1 l 0 hp (isHomogeneous_one (Fin 3) ℝ)
    hh (by simp [formalLaplacian_apply]) hl
  simpa only [map_one,ContinuousMap.one_apply,mul_one] using h

theorem laplacian_radius_power (p : Poly) (l j : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) :
    formalLaplacian (radiusSq^j*p)=C (radialCoefficient l j)*(radiusSq^(j-1)*p) := by
  cases j with
  | zero => simp [hh,radialCoefficient]
  | succ j => simpa only [Nat.add_sub_cancel] using formalLaplacian_radiusSq_pow p l hp hh j

theorem mean_laplacian_fischer (p : Poly) (d : ℕ) (hp : p ∈ fischerSpan d) :
    mean (formalLaplacian p)=(d : ℝ)*(d+1)*mean p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨l,j,h,hh,hH,hd,rfl⟩ := hp
      rw [laplacian_radius_power h l j hh hH,← smul_eq_C_mul,map_smul,
        mean_radiusSq_pow,mean_radiusSq_pow]
      simp only [smul_eq_mul]
      by_cases hl : l=0
      · subst l
        have hd' : d=2*j := by omega
        rw [hd']
        simp only [radialCoefficient,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,zero_add]
        ring
      · rw [mean_harmonic_zero h l hh hH hl]
        simp
  | zero => simp only [map_zero,mul_zero]
  | add p q hp hq ihp ihq =>
      simp only [map_add,ihp,ihq,mul_add]
  | smul a p hp ih =>
      simp only [map_smul,ih,smul_eq_mul]
      ring

theorem mean_laplacian (p : Poly) (d : ℕ) (hp : p.IsHomogeneous d) :
    mean (formalLaplacian p)=(d : ℝ)*(d+1)*mean p :=
  mean_laplacian_fischer p d (homogeneous_mem_fischerSpan p d hp)

theorem laplacian_X_mul (p : Poly) (i : Fin 3) :
    formalLaplacian (X i*p)=(2 : ℝ) • pderiv i p+X i*formalLaplacian p := by
  fin_cases i <;> simp [formalLaplacian_apply,Fin.sum_univ_three,pderiv_mul,
    smul_eq_C_mul,map_ofNat] <;> ring

theorem mean_X_harmonic_zero (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (hl : l ≠ 1) (i : Fin 3) : mean (X i*p)=0 := by
  have h := harmonic_integral_zero (X i) p 1 l (isHomogeneous_X ℝ i) hp
    (by fin_cases i <;> simp [formalLaplacian_apply,Fin.sum_univ_three]) hh hl.symm
  change (∫ n : Sphere,SpherePolynomial.polynomialMap (X i*p) n ∂angularMeasure)=0
  simpa only [map_mul,ContinuousMap.mul_apply] using h

theorem mean_harmonic_partial (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (i : Fin 3) :
    mean (pderiv i p)=(l+2 : ℝ)*mean (X i*p) := by
  have h := mean_laplacian (X i*p) (1+l) ((isHomogeneous_X ℝ i).mul hp)
  rw [laplacian_X_mul,hh,mul_zero,add_zero,map_smul] at h
  simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one] at h
  by_cases hl : l=1
  · subst l
    norm_num at h ⊢
    linarith
  · rw [mean_X_harmonic_zero p l hp hh hl i] at h ⊢
    linarith

theorem partial_radius_power (p : Poly) (j : ℕ) (i : Fin 3) :
    pderiv i (radiusSq^j*p)=(2*(j : ℝ)) • (radiusSq^(j-1)*(X i*p))+
      radiusSq^j*pderiv i p := by
  simp only [pderiv_mul,pderiv_pow,pderiv_radiusSq,smul_eq_C_mul,
    map_mul,map_ofNat,map_natCast]
  ring

theorem mean_partial_fischer (p : Poly) (d : ℕ) (hp : p ∈ fischerSpan d) (i : Fin 3) :
    mean (pderiv i p)=(d+2 : ℝ)*mean (X i*p) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨l,j,h,hh,hH,hd,rfl⟩ := hp
      rw [partial_radius_power,map_add,map_smul,mean_radiusSq_pow,mean_radiusSq_pow,
        mean_harmonic_partial h l hh hH i]
      rw [show X i*(radiusSq^j*h)=radiusSq^j*(X i*h) by ring,mean_radiusSq_pow]
      simp only [smul_eq_mul]
      have hd' : (d : ℝ)=l+2*j := by exact_mod_cast hd.symm
      rw [hd']
      ring
  | zero => simp only [map_zero,mul_zero]
  | add p q hp hq ihp ihq => simp only [map_add,mul_add,ihp,ihq]
  | smul a p hp ih =>
      simp only [Derivation.map_smul,map_smul,mul_smul_comm,ih,smul_eq_mul]
      ring

theorem mean_partial (p : Poly) (d : ℕ) (hp : p.IsHomogeneous d) (i : Fin 3) :
    mean (pderiv i p)=(d+2 : ℝ)*mean (X i*p) :=
  mean_partial_fischer p d (homogeneous_mem_fischerSpan p d hp) i

end OQ14.AngularPolynomialMean

#print axioms OQ14.AngularPolynomialMean.restriction_integrable
#print axioms OQ14.AngularPolynomialMean.mean_radiusSq_pow
#print axioms OQ14.AngularPolynomialMean.mean_harmonic_zero
#print axioms OQ14.AngularPolynomialMean.laplacian_radius_power
#print axioms OQ14.AngularPolynomialMean.mean_laplacian_fischer
#print axioms OQ14.AngularPolynomialMean.mean_laplacian
#print axioms OQ14.AngularPolynomialMean.laplacian_X_mul
#print axioms OQ14.AngularPolynomialMean.mean_X_harmonic_zero
#print axioms OQ14.AngularPolynomialMean.mean_harmonic_partial
#print axioms OQ14.AngularPolynomialMean.partial_radius_power
#print axioms OQ14.AngularPolynomialMean.mean_partial_fischer
#print axioms OQ14.AngularPolynomialMean.mean_partial
