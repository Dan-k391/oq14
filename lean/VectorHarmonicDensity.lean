import VectorHarmonicSpan

/-! Genuine continuous vector sphere density of the three harmonic sectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorHarmonicDensity
open MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
open OQ14.PolynomialVectorCalculus OQ14.VectorHarmonicSpan

def component (i : Fin 3) : C(Sphere,ℝ) →L[ℝ] C(Sphere,Space) :=
  (((1 : ℝ →L[ℝ] ℝ).smulRight (Maxwell.basis i))).compLeftContinuousCompact Sphere

theorem component_polynomial (i : Fin 3) (p : Poly) :
    component i (SpherePolynomial.polynomialMap p)=vectorMap (fun j => if j=i then p else 0) := by
  ext n j
  simp [component,vectorMap_apply,Maxwell.basis,VectorHarmonicSpan.vectorMap,
    VectorHarmonicNormalization.restriction,PiLp.smul_apply]
  split_ifs <;> simp_all

theorem component_harmonic_mem (i : Fin 3) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    component i (SpherePolynomial.polynomialMap p)∈sectorSpan := by
  rw [component_polynomial]
  apply harmonic_vector_mem _ l
  · intro j
    split_ifs
    · exact hp
    · exact (homogeneousSubmodule (Fin 3) ℝ l).zero_mem
  · intro j
    split_ifs <;> simp_all

theorem component_span_mem (i : Fin 3) (f : C(Sphere,ℝ)) (hf : f∈FischerDecomposition.harmonicSpan) :
    component i f∈sectorSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l,p,hp,hh,rfl⟩ := hf
    exact component_harmonic_mem i p l hp hh
  | zero => simpa only [map_zero] using sectorSpan.zero_mem
  | add f g hf hg ihf ihg => simpa only [map_add] using sectorSpan.add_mem ihf ihg
  | smul a f hf ih => simpa only [map_smul] using sectorSpan.smul_mem a ih

theorem component_mem_closure (i : Fin 3) (f : C(Sphere,ℝ)) :
    component i f∈sectorSpan.topologicalClosure := by
  exact map_mem_closure (component i).continuous (FischerDecomposition.harmonicSpan_dense f)
    (fun g hg => component_span_mem i g hg)

theorem sectorSpan_dense : Dense (sectorSpan : Set C(Sphere,Space)) := by
  intro f
  change f∈sectorSpan.topologicalClosure
  let coord (i : Fin 3) : C(Sphere,ℝ) := ⟨fun n => f n i,
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp f.continuous⟩
  have he : f=∑ i : Fin 3,component i (coord i) := by
    ext n j
    simp [component,coord,Maxwell.basis,PiLp.smul_apply,Fin.sum_univ_three]
    fin_cases j <;> simp
  rw [he]
  exact sectorSpan.topologicalClosure.sum_mem (fun i _ => component_mem_closure i (coord i))

def sectorL2Span : Submodule ℝ VectorHarmonicNormalization.VectorAmbient :=
  sectorSpan.map (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap

theorem sectorL2Span_dense : Dense (sectorL2Span : Set VectorHarmonicNormalization.VectorAmbient) := by
  change Dense ((ContinuousMap.toLp 2 angularMeasure ℝ) '' (sectorSpan : Set C(Sphere,Space)))
  exact (ContinuousMap.toLp_denseRange Space angularMeasure ℝ (p := 2) (by norm_num)).dense_image
    (ContinuousMap.toLp 2 angularMeasure ℝ).continuous sectorSpan_dense

end OQ14.VectorHarmonicDensity

#print axioms OQ14.VectorHarmonicDensity.component_polynomial
#print axioms OQ14.VectorHarmonicDensity.component_harmonic_mem
#print axioms OQ14.VectorHarmonicDensity.component_span_mem
#print axioms OQ14.VectorHarmonicDensity.component_mem_closure
#print axioms OQ14.VectorHarmonicDensity.sectorSpan_dense
#print axioms OQ14.VectorHarmonicDensity.sectorL2Span_dense
