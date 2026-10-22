import FischerDecomposition
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Literal homogeneous harmonic polynomial subspaces in genuine sphere L2. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SphereHarmonicBasis

open MeasureTheory OQ14.Maxwell OQ14.HarmonicPolynomial
open scoped RealInnerProductSpace

abbrev Sphere := SpherePolynomial.Sphere
abbrev angularMeasure : Measure Sphere := (volume : Measure Space).toSphere
abbrev Ambient := Lp ℝ 2 angularMeasure

def harmonicPolynomials (l : ℕ) : Submodule ℝ Poly :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℝ l ⊓ LinearMap.ker formalLaplacian

theorem harmonicPolynomials_le_totalDegree (l : ℕ) :
    harmonicPolynomials l ≤ MvPolynomial.restrictTotalDegree (Fin 3) ℝ l := by
  intro p hp
  apply (MvPolynomial.mem_restrictTotalDegree (Fin 3) l p).mpr
  by_cases hzero : p=0
  · subst p; simp
  · exact (hp.1.totalDegree hzero).le

instance harmonicPolynomials_finiteDimensional (l : ℕ) :
    FiniteDimensional ℝ (harmonicPolynomials l) :=
  FiniteDimensional.of_injective (Submodule.inclusion (harmonicPolynomials_le_totalDegree l))
    (Submodule.inclusion_injective _)

def restrictionL2 (l : ℕ) : harmonicPolynomials l →ₗ[ℝ] Ambient :=
  (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap.comp
    (SpherePolynomial.polynomialMap.toLinearMap.comp (harmonicPolynomials l).subtype)

def harmonicSpace (l : ℕ) : Submodule ℝ Ambient := LinearMap.range (restrictionL2 l)

instance harmonicSpace_finiteDimensional (l : ℕ) : FiniteDimensional ℝ (harmonicSpace l) :=
  LinearMap.finiteDimensional_range (restrictionL2 l)

abbrev Index (l : ℕ) := Fin (Module.finrank ℝ (harmonicSpace l))

def basis (l : ℕ) : OrthonormalBasis (Index l) ℝ (harmonicSpace l) :=
  stdOrthonormalBasis ℝ (harmonicSpace l)

def representative (l : ℕ) (i : Index l) : harmonicPolynomials l :=
  Classical.choose ((basis l i).property)

theorem representative_spec (l : ℕ) (i : Index l) :
    restrictionL2 l (representative l i)=(basis l i : Ambient) :=
  Classical.choose_spec ((basis l i).property)

def angular (l : ℕ) (i : Index l) : C(Sphere, ℝ) :=
  SpherePolynomial.polynomialMap (representative l i)

theorem angular_toLp (l : ℕ) (i : Index l) :
    ContinuousMap.toLp 2 angularMeasure ℝ (angular l i)=(basis l i : Ambient) :=
  representative_spec l i

theorem representative_homogeneous (l : ℕ) (i : Index l) :
    ((representative l i : harmonicPolynomials l) : Poly).IsHomogeneous l :=
  (representative l i).property.1

theorem representative_harmonic (l : ℕ) (i : Index l) :
    formalLaplacian (representative l i)=0 :=
  (representative l i).property.2

theorem angular_orthonormal (l : ℕ) :
    Orthonormal ℝ (fun i => ContinuousMap.toLp 2 angularMeasure ℝ (angular l i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [angular_toLp,angular_toLp]
  exact orthonormal_iff_ite.mp (basis l).orthonormal i j

theorem angular_integral_pair (l : ℕ) (i j : Index l) :
    (∫ n : Sphere, angular l i n*angular l j n ∂angularMeasure)=if i=j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (angular_orthonormal l) j i
  rw [ContinuousMap.inner_toLp] at h
  simpa only [conj_trivial,eq_comm] using h

theorem angular_integral_sq (l : ℕ) (i : Index l) :
    (∫ n : Sphere, angular l i n^2 ∂angularMeasure)=1 := by
  simpa only [sq,if_pos rfl] using angular_integral_pair l i i

def polynomialVector (l : ℕ) (p : harmonicPolynomials l) : harmonicSpace l :=
  ⟨restrictionL2 l p, ⟨p,rfl⟩⟩

theorem restriction_expansion (l : ℕ) (p : harmonicPolynomials l) :
    SpherePolynomial.polynomialMap p=∑ i : Index l,
      (basis l).repr (polynomialVector l p) i • angular l i := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) angularMeasure
  simp only [map_sum,map_smul,angular_toLp]
  have h := congrArg (harmonicSpace l).subtype ((basis l).sum_repr (polynomialVector l p))
  simpa only [map_sum,map_smul,Submodule.subtype_apply] using h.symm

theorem representative_ne_zero (l : ℕ) (i : Index l) : (representative l i : Poly) ≠ 0 := by
  intro hzero
  have h := angular_integral_sq l i
  simp only [angular,hzero,map_zero,ContinuousMap.zero_apply,zero_pow (by norm_num : (2 : ℕ) ≠ 0),integral_zero] at h
  exact zero_ne_one h

def allAngular : Set C(Sphere, ℝ) := Set.range (fun a : Σ l, Index l => angular a.1 a.2)

def angularSpan : Submodule ℝ C(Sphere, ℝ) := Submodule.span ℝ allAngular

theorem restriction_mem_angularSpan (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) : SpherePolynomial.polynomialMap p ∈ angularSpan := by
  rw [restriction_expansion l ⟨p,⟨hp,hh⟩⟩]
  apply angularSpan.sum_mem
  intro i _
  apply angularSpan.smul_mem
  exact Submodule.subset_span ⟨⟨l,i⟩,rfl⟩

theorem angularSpan_dense : Dense (angularSpan : Set C(Sphere, ℝ)) := by
  apply FischerDecomposition.harmonicSpan_dense.mono
  apply Submodule.span_le.mpr
  rintro f ⟨l,p,hp,hh,rfl⟩
  exact restriction_mem_angularSpan l p hp hh

def angularL2Span : Submodule ℝ Ambient :=
  angularSpan.map (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap

theorem angularL2Span_dense : Dense (angularL2Span : Set Ambient) := by
  change Dense ((ContinuousMap.toLp 2 angularMeasure ℝ) '' (angularSpan : Set C(Sphere, ℝ)))
  exact (ContinuousMap.toLp_denseRange ℝ angularMeasure ℝ (p := 2) (by norm_num)).dense_image
    (ContinuousMap.toLp 2 angularMeasure ℝ).continuous angularSpan_dense

end OQ14.SphereHarmonicBasis

#print axioms OQ14.SphereHarmonicBasis.harmonicPolynomials_le_totalDegree
#print axioms OQ14.SphereHarmonicBasis.harmonicPolynomials_finiteDimensional
#print axioms OQ14.SphereHarmonicBasis.harmonicSpace_finiteDimensional
#print axioms OQ14.SphereHarmonicBasis.representative_spec
#print axioms OQ14.SphereHarmonicBasis.angular_toLp
#print axioms OQ14.SphereHarmonicBasis.representative_homogeneous
#print axioms OQ14.SphereHarmonicBasis.representative_harmonic
#print axioms OQ14.SphereHarmonicBasis.angular_orthonormal
#print axioms OQ14.SphereHarmonicBasis.angular_integral_pair
#print axioms OQ14.SphereHarmonicBasis.angular_integral_sq
#print axioms OQ14.SphereHarmonicBasis.restriction_expansion
#print axioms OQ14.SphereHarmonicBasis.representative_ne_zero
#print axioms OQ14.SphereHarmonicBasis.restriction_mem_angularSpan
#print axioms OQ14.SphereHarmonicBasis.angularSpan_dense
#print axioms OQ14.SphereHarmonicBasis.angularL2Span_dense
