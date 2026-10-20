import HarmonicPolynomial

/-! # Finite harmonic decomposition of actual real polynomials -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.FischerDecomposition
open MvPolynomial OQ14.HarmonicPolynomial
abbrev Poly := HarmonicPolynomial.Poly

def generators (n : ℕ) : Set Poly :=
  {p | ∃ (l j : ℕ) (h : Poly), h.IsHomogeneous l ∧ formalLaplacian h = 0 ∧
    l + 2*j = n ∧ p = radiusSq^j*h}

def fischerSpan (n : ℕ) : Submodule ℝ Poly := Submodule.span ℝ (generators n)

theorem harmonic_mem (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n)
    (harm : formalLaplacian p = 0) : p ∈ fischerSpan n := by
  apply Submodule.subset_span
  exact ⟨n, 0, p, hp, harm, by omega, by simp⟩

theorem formalLaplacian_low_degree (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n)
    (hn : n ≤ 1) : formalLaplacian p = 0 := by
  rw [formalLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hh : (pderiv i p).IsHomogeneous 0 := by
    simpa only [show n-1=0 by omega] using hp.pderiv (i := i)
  have hc := (totalDegree_eq_zero_iff_eq_C).mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hh)
  rw [hc, pderiv_C]

theorem laplacian_preimage (n : ℕ) (hn : 2 ≤ n) (p : Poly)
    (hp : p ∈ fischerSpan (n-2)) :
    ∃ q : Poly, q.IsHomogeneous n ∧ formalLaplacian q = p ∧ q ∈ fischerSpan n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨l,j,h,hh,harm,hdegree,rfl⟩ := hp
    let c := radialCoefficient l (j+1)
    have hc : c ≠ 0 := ne_of_gt (radialCoefficient_positive l j)
    have hdegree' : l+2*(j+1)=n := by omega
    refine ⟨c⁻¹ • (radiusSq^(j+1)*h), ?_, ?_, ?_⟩
    · rw [smul_eq_C_mul]
      exact (hdegree' ▸ radiusSq_pow_homogeneous h l (j+1) hh).C_mul _
    · rw [map_smul, formalLaplacian_radiusSq_pow h l hh harm]
      rw [← smul_eq_C_mul, smul_smul]
      simp [c, hc]
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨l,j+1,h,hh,harm,hdegree',rfl⟩
  | zero => exact ⟨0, isHomogeneous_zero (Fin 3) ℝ n, map_zero _, Submodule.zero_mem _⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨u,hu,hlu,hmu⟩ := ihp
    obtain ⟨v,hv,hlv,hmv⟩ := ihq
    exact ⟨u+v, hu.add hv, by rw [map_add,hlu,hlv], Submodule.add_mem _ hmu hmv⟩
  | smul a p hp ih =>
    obtain ⟨u,hu,hlu,hmu⟩ := ih
    refine ⟨a • u, ?_, by rw [map_smul,hlu], Submodule.smul_mem _ a hmu⟩
    rw [smul_eq_C_mul]
    exact hu.C_mul a

theorem homogeneous_mem_fischerSpan (p : Poly) (n : ℕ) (hp : p.IsHomogeneous n) :
    p ∈ fischerSpan n := by
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n ≤ 1
    · exact harmonic_mem p n hp (formalLaplacian_low_degree p n hp hn)
    · have hn' : 2 ≤ n := by omega
      have hl := ih (n-2) (by omega) (formalLaplacian p)
        (formalLaplacian_homogeneous p n hp)
      obtain ⟨q,hq,hlq,hmq⟩ := laplacian_preimage n hn' (formalLaplacian p) hl
      have hh : formalLaplacian (p-q) = 0 := by rw [map_sub,hlq,sub_self]
      have hhom : (p-q).IsHomogeneous n := (homogeneousSubmodule (Fin 3) ℝ n).sub_mem hp hq
      have hm := (fischerSpan n).add_mem (harmonic_mem (p-q) n hhom hh) hmq
      simpa only [sub_add_cancel] using hm


abbrev Sphere := SpherePolynomial.Sphere

def harmonicRestrictions : Set C(Sphere, ℝ) :=
  {f | ∃ (n : ℕ) (p : Poly), p.IsHomogeneous n ∧ formalLaplacian p = 0 ∧
    f = SpherePolynomial.polynomialMap p}

def harmonicSpan : Submodule ℝ C(Sphere, ℝ) := Submodule.span ℝ harmonicRestrictions

theorem radiusSq_on_sphere : SpherePolynomial.polynomialMap radiusSq = 1 := by
  ext n
  rw [SpherePolynomial.polynomialMap_apply]
  have hn : ‖(n : OQ14.Maxwell.Space)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using n.property
  have hs : ∑ i : Fin 3, (n : OQ14.Maxwell.Space) i ^ 2 = ‖(n : OQ14.Maxwell.Space)‖^2 := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (n : OQ14.Maxwell.Space)).symm
  simpa [radiusSq, hn] using hs

theorem fischer_restriction_mem (p : Poly) (n : ℕ) (hp : p ∈ fischerSpan n) :
    SpherePolynomial.polynomialMap p ∈ harmonicSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨l,j,h,hh,harm,hdegree,rfl⟩ := hp
    rw [map_mul, map_pow, radiusSq_on_sphere, one_pow, one_mul]
    exact Submodule.subset_span ⟨l,h,hh,harm,rfl⟩
  | zero => simp only [map_zero]; exact harmonicSpan.zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using harmonicSpan.add_mem ihp ihq
  | smul a p hp ih => simpa only [map_smul] using harmonicSpan.smul_mem a ih

theorem polynomial_restriction_mem (p : Poly) :
    SpherePolynomial.polynomialMap p ∈ harmonicSpan := by
  have hs : SpherePolynomial.polynomialMap p =
      ∑ n ∈ Finset.range (p.totalDegree+1),
        SpherePolynomial.polynomialMap (homogeneousComponent n p) := by
    rw [← map_sum, sum_homogeneousComponent]
  rw [hs]
  apply harmonicSpan.sum_mem
  intro n _
  exact fischer_restriction_mem _ n
    (homogeneous_mem_fischerSpan _ n (homogeneousComponent_isHomogeneous n p))

theorem harmonicSpan_dense : Dense (harmonicSpan : Set C(Sphere, ℝ)) := by
  apply SpherePolynomial.polynomialMap_denseRange.mono
  rintro f ⟨p,rfl⟩
  exact polynomial_restriction_mem p


theorem evaluate_smul (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (r : ℝ) (x : OQ14.Maxwell.Space) :
    evaluate p (r • x) = r^l * evaluate p x := by
  classical
  simp only [evaluate, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : (∑ i ∈ d.support, d i) = l := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, nsmul_eq_mul, mul_one] using
      hp (Finsupp.mem_support_iff.mp hd)
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem complexEvaluate_smul (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (r : ℝ) (x : OQ14.Maxwell.Space) :
    complexEvaluate p (r • x) = (r : ℂ)^l * complexEvaluate p x := by
  simp only [complexEvaluate, evaluate_smul p l hp, Complex.ofReal_mul, Complex.ofReal_pow]

theorem complexEvaluate_harmonic (p : Poly) (harm : formalLaplacian p = 0)
    (x : OQ14.Maxwell.Space) :
    OQ14.ExteriorHelmholtz.laplacian (complexEvaluate p) x = 0 := by
  rw [complexEvaluate_laplacian, harm]
  simp [evaluate]
end OQ14.FischerDecomposition

#print axioms OQ14.FischerDecomposition.harmonic_mem
#print axioms OQ14.FischerDecomposition.formalLaplacian_low_degree
#print axioms OQ14.FischerDecomposition.laplacian_preimage
#print axioms OQ14.FischerDecomposition.homogeneous_mem_fischerSpan
#print axioms OQ14.FischerDecomposition.radiusSq_on_sphere
#print axioms OQ14.FischerDecomposition.fischer_restriction_mem
#print axioms OQ14.FischerDecomposition.polynomial_restriction_mem
#print axioms OQ14.FischerDecomposition.harmonicSpan_dense
#print axioms OQ14.FischerDecomposition.evaluate_smul
#print axioms OQ14.FischerDecomposition.complexEvaluate_smul
#print axioms OQ14.FischerDecomposition.complexEvaluate_harmonic
