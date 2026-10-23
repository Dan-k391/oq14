import OutgoingFarSeries

/-! Actual scalar coordinate maps commute with the genuine sphere L2 embeddings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereVectorComponents
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere

def coordinate (i : Fin 3) : ComplexVectorSphere.Ambient →L[ℂ] Lp ℂ 2 angularMeasure :=
  (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).compLpL 2 angularMeasure

def complexComponent (v : C(Sphere,ComplexVectorSphere.Vector)) (i : Fin 3) : C(Sphere,ℂ) :=
  ⟨fun n => v n i,(EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).continuous.comp v.continuous⟩

def realComponent (v : C(Sphere,Space)) (i : Fin 3) : C(Sphere,ℂ) :=
  ⟨fun n => (v n i : ℂ),Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp v.continuous)⟩

theorem complexComponent_toLp (v : C(Sphere,ComplexVectorSphere.Vector)) (i : Fin 3) :
    ContinuousMap.toLp 2 angularMeasure ℂ (complexComponent v i)=
      coordinate i (ContinuousMap.toLp 2 angularMeasure ℂ v) := by
  apply Lp.ext
  filter_upwards [(complexComponent v i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    v.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).coeFn_compLpL
      (ContinuousMap.toLp 2 angularMeasure ℂ v)] with n hc hv he
  change coordinate i (ContinuousMap.toLp 2 angularMeasure ℂ v) n=
    (ContinuousMap.toLp 2 angularMeasure ℂ v) n i at he
  rw [hc,he,hv]
  rfl

theorem realComponent_toLp (v : C(Sphere,Space)) (i : Fin 3) :
    ContinuousMap.toLp 2 angularMeasure ℂ (realComponent v i)=
      coordinate i (realLift (ContinuousMap.toLp 2 angularMeasure ℝ v)) := by
  apply Lp.ext
  filter_upwards [(realComponent v i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    v.coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure,
    embedVector.coeFn_compLpL (ContinuousMap.toLp 2 angularMeasure ℝ v),
    (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).coeFn_compLpL
      (realLift (ContinuousMap.toLp 2 angularMeasure ℝ v))] with n hc hv he hi
  change realLift (ContinuousMap.toLp 2 angularMeasure ℝ v) n=
    embedVector ((ContinuousMap.toLp 2 angularMeasure ℝ v) n) at he
  change coordinate i (realLift (ContinuousMap.toLp 2 angularMeasure ℝ v)) n=
    realLift (ContinuousMap.toLp 2 angularMeasure ℝ v) n i at hi
  rw [hc,hi,he,hv]
  rfl

end OQ14.SphereVectorComponents

#print axioms OQ14.SphereVectorComponents.complexComponent_toLp
#print axioms OQ14.SphereVectorComponents.realComponent_toLp
