import SphereHarmonicHilbert

/-! Actual complexification of the complete real angular basis. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.ComplexHarmonicBasis

open MeasureTheory Set OQ14.SphereHarmonicBasis OQ14.SphereHarmonicOrthogonality
  OQ14.SphereHarmonicHilbert
open scoped ComplexInnerProductSpace Topology

abbrev ComplexAmbient := Lp ℂ 2 angularMeasure

def realLift : Ambient →L[ℝ] ComplexAmbient := Complex.ofRealCLM.compLpL 2 angularMeasure

def realPart : ComplexAmbient →L[ℝ] Ambient := Complex.reCLM.compLpL 2 angularMeasure

def imagPart : ComplexAmbient →L[ℝ] Ambient := Complex.imCLM.compLpL 2 angularMeasure

def vector (a : TotalIndex) : ComplexAmbient := realLift (allVectors a)

theorem realLift_inner (u v : Ambient) :
    ⟪realLift u,realLift v⟫=((@inner ℝ Ambient _ u v : ℝ) : ℂ) := by
  rw [L2.inner_def,L2.inner_def,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL u,Complex.ofRealCLM.coeFn_compLpL v] with x hu hv
  simp only [realLift,hu,hv,Complex.ofRealCLM_apply,RCLike.inner_apply,
    Complex.conj_ofReal,Complex.ofReal_mul,conj_trivial]

theorem vector_orthonormal : Orthonormal ℂ vector := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [vector,vector,realLift_inner,orthonormal_iff_ite.mp allVectors_orthonormal]
  split_ifs <;> simp

theorem real_imag_decomposition (u : ComplexAmbient) :
    u=realLift (realPart u)+Complex.I • realLift (imagPart u) := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLpL u,Complex.imCLM.coeFn_compLpL u,
    Complex.ofRealCLM.coeFn_compLpL (realPart u),Complex.ofRealCLM.coeFn_compLpL (imagPart u),
    Lp.coeFn_add (realLift (realPart u)) (Complex.I • realLift (imagPart u)),
    Lp.coeFn_smul Complex.I (realLift (imagPart u))] with x hr hi hrr hii ha hs
  simp only [realLift,realPart,imagPart] at *
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hrr,hii,hr,hi]
  simp only [Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  simpa only [mul_comm] using (Complex.re_add_im (u x)).symm

theorem realLift_span (u : Ambient) (hu : u ∈ Submodule.span ℝ (Set.range allVectors)) :
    realLift u ∈ Submodule.span ℂ (Set.range vector) := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨a,rfl⟩
      exact Submodule.subset_span ⟨a,rfl⟩
  | zero => simpa only [map_zero] using (Submodule.span ℂ (Set.range vector)).zero_mem
  | add u v _ _ hu hv =>
      simpa only [map_add] using (Submodule.span ℂ (Set.range vector)).add_mem hu hv
  | smul r u _ hu =>
      rw [map_smul]
      exact (Submodule.span ℂ (Set.range vector)).smul_mem (r : ℂ) hu

theorem span_vector_dense :
    (Submodule.span ℂ (Set.range vector)).topologicalClosure=⊤ := by
  have hd : Dense (Submodule.span ℝ (Set.range allVectors) : Set Ambient) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_allVectors_dense
  have hr (u : Ambient) : realLift u ∈ (Submodule.span ℂ (Set.range vector)).topologicalClosure := by
    exact map_mem_closure realLift.continuous (hd u) (fun v hv => realLift_span v hv)
  apply top_unique
  intro u _
  rw [real_imag_decomposition u]
  exact (Submodule.span ℂ (Set.range vector)).topologicalClosure.add_mem
    (hr (realPart u)) ((Submodule.span ℂ (Set.range vector)).topologicalClosure.smul_mem
      Complex.I (hr (imagPart u)))

def hilbertBasis : HilbertBasis TotalIndex ℂ ComplexAmbient :=
  HilbertBasis.mk vector_orthonormal (by rw [span_vector_dense])

theorem hilbertBasis_apply (a : TotalIndex) : hilbertBasis a=vector a := by
  exact congrFun (HilbertBasis.coe_mk vector_orthonormal (by rw [span_vector_dense])) a

theorem expansion (u : ComplexAmbient) :
    HasSum (fun a : TotalIndex => ⟪vector a,u⟫ • vector a) u := by
  simpa only [HilbertBasis.repr_apply_apply,hilbertBasis_apply] using hilbertBasis.hasSum_repr u

def complexAngular (a : TotalIndex) : C(Sphere,ℂ) :=
  ⟨fun n => (angular a.1 a.2 n : ℂ),Complex.continuous_ofReal.comp (angular a.1 a.2).continuous⟩

theorem vector_toLp (a : TotalIndex) :
    vector a=ContinuousMap.toLp 2 angularMeasure ℂ (complexAngular a) := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (allVectors a),
    (angular a.1 a.2).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure,
    (complexAngular a).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hl hr hc
  change vector a n=(allVectors a n : ℂ) at hl
  change allVectors a n=angular a.1 a.2 n at hr
  rw [hl,hr,hc]
  rfl

theorem coefficient_integral (f : C(Sphere,ℂ)) (a : TotalIndex) :
    ⟪vector a,ContinuousMap.toLp 2 angularMeasure ℂ f⟫=
      ∫ n : Sphere,(angular a.1 a.2 n : ℂ)*f n ∂angularMeasure := by
  rw [vector_toLp,ContinuousMap.inner_toLp]
  simp only [complexAngular,ContinuousMap.coe_mk,Complex.conj_ofReal,mul_comm]

theorem continuous_expansion (f : C(Sphere,ℂ)) :
    HasSum (fun a : TotalIndex =>
      (∫ n : Sphere,(angular a.1 a.2 n : ℂ)*f n ∂angularMeasure) • vector a)
      (ContinuousMap.toLp 2 angularMeasure ℂ f) := by
  simpa only [coefficient_integral] using expansion (ContinuousMap.toLp 2 angularMeasure ℂ f)

end OQ14.ComplexHarmonicBasis

#print axioms OQ14.ComplexHarmonicBasis.realLift_inner
#print axioms OQ14.ComplexHarmonicBasis.vector_orthonormal
#print axioms OQ14.ComplexHarmonicBasis.real_imag_decomposition
#print axioms OQ14.ComplexHarmonicBasis.realLift_span
#print axioms OQ14.ComplexHarmonicBasis.span_vector_dense
#print axioms OQ14.ComplexHarmonicBasis.hilbertBasis_apply
#print axioms OQ14.ComplexHarmonicBasis.expansion

#print axioms OQ14.ComplexHarmonicBasis.vector_toLp
#print axioms OQ14.ComplexHarmonicBasis.coefficient_integral
#print axioms OQ14.ComplexHarmonicBasis.continuous_expansion
