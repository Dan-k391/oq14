import SphereHarmonicOrthogonality
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Genuine complete scalar harmonic basis for the actual sphere measure. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SphereHarmonicHilbert

open MeasureTheory Set OQ14.SphereHarmonicBasis OQ14.SphereHarmonicOrthogonality
open scoped RealInnerProductSpace Topology

abbrev TotalIndex := Σ l, Index l

theorem span_allVectors : Submodule.span ℝ (Set.range allVectors)=angularL2Span := by
  unfold angularL2Span angularSpan
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [allAngular,Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨angular a.1 a.2,⟨a,rfl⟩,rfl⟩
  · rintro ⟨f,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

theorem span_allVectors_dense :
    (Submodule.span ℝ (Set.range allVectors)).topologicalClosure=⊤ := by
  rw [span_allVectors]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp angularL2Span_dense

def hilbertBasis : HilbertBasis TotalIndex ℝ Ambient :=
  HilbertBasis.mk allVectors_orthonormal (by rw [span_allVectors_dense])

theorem hilbertBasis_apply (a : TotalIndex) : hilbertBasis a=allVectors a := by
  exact congrFun (HilbertBasis.coe_mk allVectors_orthonormal
    (by rw [span_allVectors_dense])) a

theorem expansion (u : Ambient) :
    HasSum (fun a : TotalIndex => ⟪allVectors a,u⟫ • allVectors a) u := by
  simpa only [HilbertBasis.repr_apply_apply,hilbertBasis_apply] using hilbertBasis.hasSum_repr u

theorem parseval (u : Ambient) :
    HasSum (fun a : TotalIndex => ⟪allVectors a,u⟫^2) (‖u‖^2) := by
  have h := hilbertBasis.hasSum_inner_mul_inner u u
  simpa only [hilbertBasis_apply,real_inner_comm,← sq,real_inner_self_eq_norm_sq] using h

theorem coefficient_integral (f : C(Sphere,ℝ)) (a : TotalIndex) :
    ⟪allVectors a,ContinuousMap.toLp 2 angularMeasure ℝ f⟫=
      ∫ n : Sphere,angular a.1 a.2 n*f n ∂angularMeasure := by
  unfold allVectors
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial,mul_comm]

theorem continuous_expansion (f : C(Sphere,ℝ)) :
    HasSum (fun a : TotalIndex =>
      (∫ n : Sphere,angular a.1 a.2 n*f n ∂angularMeasure) • allVectors a)
      (ContinuousMap.toLp 2 angularMeasure ℝ f) := by
  simpa only [coefficient_integral] using expansion (ContinuousMap.toLp 2 angularMeasure ℝ f)

end OQ14.SphereHarmonicHilbert

#print axioms OQ14.SphereHarmonicHilbert.span_allVectors
#print axioms OQ14.SphereHarmonicHilbert.span_allVectors_dense
#print axioms OQ14.SphereHarmonicHilbert.hilbertBasis_apply
#print axioms OQ14.SphereHarmonicHilbert.expansion
#print axioms OQ14.SphereHarmonicHilbert.parseval
#print axioms OQ14.SphereHarmonicHilbert.coefficient_integral
#print axioms OQ14.SphereHarmonicHilbert.continuous_expansion
