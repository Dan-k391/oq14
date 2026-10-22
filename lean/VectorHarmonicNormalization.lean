import AngularHarmonicEnergy
import DebyeRadialTrace

/-! Genuine vector sphere L2 normalization of actual angular harmonic fields. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace OQ14.VectorHarmonicNormalization

open MeasureTheory Set MvPolynomial OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.AngularPolynomialMean OQ14.AngularHarmonicEnergy
open scoped RealInnerProductSpace

abbrev VectorAmbient := Lp OQ14.Maxwell.Space 2 angularMeasure

def restriction (v : Fin 3 → Poly) : C(Sphere,OQ14.Maxwell.Space) where
  toFun n := (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => SpherePolynomial.polynomialMap (v i) n)
  continuous_toFun := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
    (continuous_pi (fun i => (SpherePolynomial.polynomialMap (v i)).continuous))

def restrictionL2 (v : Fin 3 → Poly) : VectorAmbient :=
  ContinuousMap.toLp 2 angularMeasure ℝ (restriction v)

theorem restriction_inner (v w : Fin 3 → Poly) :
    ⟪restrictionL2 v,restrictionL2 w⟫=mean (polynomialDot v w) := by
  rw [L2.inner_def]
  change (∫ n : Sphere,⟪restrictionL2 v n,restrictionL2 w n⟫ ∂angularMeasure)=
    ∫ n : Sphere,SpherePolynomial.polynomialMap (polynomialDot v w) n ∂angularMeasure
  apply integral_congr_ae
  filter_upwards [(restriction v).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure,
    (restriction w).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hv hw
  change restrictionL2 v n=restriction v n at hv
  change restrictionL2 w n=restriction w n at hw
  rw [hv,hw,PiLp.inner_apply]
  simp [restriction,polynomialDot,map_sum,map_mul,RCLike.inner_apply,mul_comm]

theorem representative_pair_mean (l : ℕ) (i j : Index l) :
    mean ((representative l i : Poly)*representative l j)=if i=j then 1 else 0 := by
  change (∫ n : Sphere,SpherePolynomial.polynomialMap
    ((representative l i : Poly)*representative l j) n ∂angularMeasure)=_
  simpa only [map_mul,ContinuousMap.mul_apply,angular] using angular_integral_pair l i j

def poloidal (l : ℕ) (i : Index l) : VectorAmbient :=
  restrictionL2 (tangential (representative l i) l)

def toroidalField (l : ℕ) (i : Index l) : VectorAmbient :=
  restrictionL2 (toroidal (representative l i))

theorem poloidal_inner_same (l : ℕ) (i j : Index l) :
    ⟪poloidal l i,poloidal l j⟫=(l : ℝ)*(l+1)*(if i=j then 1 else 0) := by
  rw [poloidal,poloidal,restriction_inner,tangential_energy _ _ l
    (representative_homogeneous l i) (representative_homogeneous l j)
    (representative_harmonic l i) (representative_harmonic l j),representative_pair_mean]

theorem toroidal_inner_same (l : ℕ) (i j : Index l) :
    ⟪toroidalField l i,toroidalField l j⟫=(l : ℝ)*(l+1)*(if i=j then 1 else 0) := by
  rw [toroidalField,toroidalField,restriction_inner,toroidal_energy _ _ l
    (representative_homogeneous l i) (representative_homogeneous l j)
    (representative_harmonic l i) (representative_harmonic l j),representative_pair_mean]

theorem poloidal_inner_cross (l m : ℕ) (i : Index l) (j : Index m) (hlm : l ≠ m) :
    ⟪poloidal l i,poloidal m j⟫=0 := by
  rw [poloidal,poloidal,restriction_inner]
  exact tangential_cross_degree _ _ l m (representative_homogeneous l i) (representative_homogeneous m j)
    (representative_harmonic l i) (representative_harmonic m j) hlm

theorem toroidal_inner_cross (l m : ℕ) (i : Index l) (j : Index m) (hlm : l ≠ m) :
    ⟪toroidalField l i,toroidalField m j⟫=0 := by
  rw [toroidalField,toroidalField,restriction_inner]
  exact toroidal_cross_degree _ _ l m (representative_homogeneous l i) (representative_homogeneous m j)
    (representative_harmonic l i) (representative_harmonic m j) hlm

theorem mixed_inner (l m : ℕ) (i : Index l) (j : Index m) :
    ⟪toroidalField l i,poloidal m j⟫=0 := by
  rw [toroidalField,poloidal,restriction_inner]
  exact mixed_mean_zero _ _ l m (representative_homogeneous l i) (representative_homogeneous m j)

abbrev PositiveIndex := Σ l : ℕ,Index (l+1)

def normalizer (l : ℕ) : ℝ := (Real.sqrt ((l+1 : ℝ)*(l+2)))⁻¹

theorem normalizer_identity (l : ℕ) : normalizer l*normalizer l*((l+1 : ℝ)*(l+2))=1 := by
  have hc : 0 < (l+1 : ℝ)*(l+2) := by positivity
  unfold normalizer
  rw [← mul_inv,← pow_two,Real.sq_sqrt hc.le,inv_mul_cancel₀ (ne_of_gt hc)]

def normalizedP (a : PositiveIndex) : VectorAmbient := normalizer a.1 • poloidal (a.1+1) a.2

def normalizedT (a : PositiveIndex) : VectorAmbient := normalizer a.1 • toroidalField (a.1+1) a.2

theorem normalizedP_orthonormal : Orthonormal ℝ normalizedP := by
  rw [orthonormal_iff_ite]
  rintro ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l=m
  · subst m
    simp only [normalizedP,real_inner_smul_left,real_inner_smul_right,poloidal_inner_same,
      Sigma.mk.inj_iff,heq_eq_eq,eq_self_iff_true,true_and,Nat.cast_add,Nat.cast_one]
    by_cases hij : i=j
    · rw [if_pos hij]
      convert normalizer_identity l using 1; ring
    · simp only [if_neg hij,mul_zero]
  · have hdeg : l+1 ≠ m+1 := by omega
    rw [if_neg (fun h => hlm (congrArg Sigma.fst h))]
    simp only [normalizedP,real_inner_smul_left,real_inner_smul_right,
      poloidal_inner_cross (l+1) (m+1) i j hdeg,mul_zero]

theorem normalizedT_orthonormal : Orthonormal ℝ normalizedT := by
  rw [orthonormal_iff_ite]
  rintro ⟨l,i⟩ ⟨m,j⟩
  by_cases hlm : l=m
  · subst m
    simp only [normalizedT,real_inner_smul_left,real_inner_smul_right,toroidal_inner_same,
      Sigma.mk.inj_iff,heq_eq_eq,eq_self_iff_true,true_and,Nat.cast_add,Nat.cast_one]
    by_cases hij : i=j
    · rw [if_pos hij]
      convert normalizer_identity l using 1; ring
    · simp only [if_neg hij,mul_zero]
  · have hdeg : l+1 ≠ m+1 := by omega
    rw [if_neg (fun h => hlm (congrArg Sigma.fst h))]
    simp only [normalizedT,real_inner_smul_left,real_inner_smul_right,
      toroidal_inner_cross (l+1) (m+1) i j hdeg,mul_zero]

theorem normalized_mixed (a b : PositiveIndex) : ⟪normalizedT a,normalizedP b⟫=0 := by
  simp only [normalizedT,normalizedP,real_inner_smul_left,real_inner_smul_right,mixed_inner,mul_zero]

def polarized : PositiveIndex ⊕ PositiveIndex → VectorAmbient := Sum.elim normalizedP normalizedT

theorem polarized_orthonormal : Orthonormal ℝ polarized := by
  rw [orthonormal_iff_ite]
  rintro (a|a) (b|b)
  · simpa only [polarized,Sum.elim_inl,Sum.inl.injEq] using
      orthonormal_iff_ite.mp normalizedP_orthonormal a b
  · simp only [polarized,Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,if_false]
    rw [real_inner_comm,normalized_mixed]
  · simp only [polarized,Sum.elim_inl,Sum.elim_inr,Sum.inr_ne_inl,if_false,normalized_mixed]
  · simpa only [polarized,Sum.elim_inr,Sum.inr.injEq] using
      orthonormal_iff_ite.mp normalizedT_orthonormal a b

theorem restriction_toroidal_component (p : Poly) (n : Sphere) (i : Fin 3) :
    ((restriction (toroidal p) n) i : ℂ)=OQ14.DebyeRadialTrace.angularToroidal p (n : OQ14.Maxwell.Space) i := by
  fin_cases i <;> simp [restriction,toroidal,OQ14.DebyeRadialTrace.angularToroidal,
    complexEvaluate_partial,SpherePolynomial.polynomialMap_apply,evaluate]

theorem restriction_poloidal_component (p : Poly) (l : ℕ) (n : Sphere) (i : Fin 3) :
    ((restriction (tangential p l) n) i : ℂ)=
      OQ14.DebyeRadialTrace.angularPoloidal p l (n : OQ14.Maxwell.Space) i := by
  have hn : ‖(n : OQ14.Maxwell.Space)‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  simp [restriction,tangential,OQ14.DebyeRadialTrace.angularPoloidal,hn,
    complexEvaluate_partial,SpherePolynomial.polynomialMap_apply,complexEvaluate,evaluate,smul_eq_C_mul]
  ring

theorem restriction_toroidal_tangent (p : Poly) (n : Sphere) :
    (∑ i : Fin 3,(n : OQ14.Maxwell.Space) i*(restriction (toroidal p) n) i)=0 := by
  have h := congrArg (MvPolynomial.eval (fun i => (n : OQ14.Maxwell.Space) i)) (toroidal_radial_zero p)
  simpa [restriction,SpherePolynomial.polynomialMap_apply] using h

theorem restriction_poloidal_tangent (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (n : Sphere) :
    (∑ i : Fin 3,(n : OQ14.Maxwell.Space) i*(restriction (tangential p l) n) i)=0 := by
  have he := congrArg (MvPolynomial.eval (fun i => (n : OQ14.Maxwell.Space) i)) (euler p l hp)
  have hs := congrArg (fun f : C(Sphere,ℝ) => f n) OQ14.FischerDecomposition.radiusSq_on_sphere
  simp [radiusSq,SpherePolynomial.polynomialMap_apply,Fin.sum_univ_three] at hs
  simp [smul_eq_C_mul,Fin.sum_univ_three] at he
  simp [restriction,tangential,Fin.sum_univ_three,SpherePolynomial.polynomialMap_apply,smul_eq_C_mul]
  linear_combination he-(l : ℝ)*MvPolynomial.eval (fun i => (n : OQ14.Maxwell.Space) i) p*hs

end OQ14.VectorHarmonicNormalization

#print axioms OQ14.VectorHarmonicNormalization.restriction_inner
#print axioms OQ14.VectorHarmonicNormalization.representative_pair_mean
#print axioms OQ14.VectorHarmonicNormalization.poloidal_inner_same
#print axioms OQ14.VectorHarmonicNormalization.toroidal_inner_same
#print axioms OQ14.VectorHarmonicNormalization.poloidal_inner_cross
#print axioms OQ14.VectorHarmonicNormalization.toroidal_inner_cross
#print axioms OQ14.VectorHarmonicNormalization.mixed_inner
#print axioms OQ14.VectorHarmonicNormalization.normalizer_identity
#print axioms OQ14.VectorHarmonicNormalization.normalizedP_orthonormal
#print axioms OQ14.VectorHarmonicNormalization.normalizedT_orthonormal
#print axioms OQ14.VectorHarmonicNormalization.normalized_mixed
#print axioms OQ14.VectorHarmonicNormalization.polarized_orthonormal
#print axioms OQ14.VectorHarmonicNormalization.restriction_toroidal_component
#print axioms OQ14.VectorHarmonicNormalization.restriction_poloidal_component
#print axioms OQ14.VectorHarmonicNormalization.restriction_toroidal_tangent
#print axioms OQ14.VectorHarmonicNormalization.restriction_poloidal_tangent
