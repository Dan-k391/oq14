import SphereVectorComponents

/-! The actual signed source far-amplitude series reconstructs the genuine free dyadic amplitude. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FreeFarFieldExpansion
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open OQ14.VectorHarmonicNormalization OQ14.FreeSourceCoefficients OQ14.SphereVectorComponents
open scoped ComplexInnerProductSpace

def freeMap (y : Space) (i j : Fin 3) : C(Sphere,ℂ) :=
  ((4*Real.pi : ℂ)⁻¹) • complexComponent (TransversePlaneFields.plane 1 y j) i

def farMap (a : PositiveIndex) (y : Space) (i j : Fin 3) : C(Sphere,ℂ) :=
  (tmCoefficient a y j*SourceRadiation.phase (a.1+1)) •
      realComponent (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩) i+
    (teCoefficient a y j*(-SourceRadiation.phase (a.1+1))) •
      realComponent (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩) i

theorem freeMap_toLp (y : Space) (i j : Fin 3) :
    ContinuousMap.toLp 2 angularMeasure ℂ (freeMap y i j)=SphereVectorComponents.coordinate i (freeAmplitude y j) := by
  rw [freeMap,map_smul,complexComponent_toLp,freeAmplitude,map_smul]
  rfl

theorem freeAmplitude_tangent (y : Space) (j : Fin 3) : IsTangential (freeAmplitude y j) := by
  filter_upwards [TransversePlaneFields.field_tangent 1 y j,
    Lp.coeFn_smul ((4*Real.pi : ℂ)⁻¹) (TransversePlaneFields.field 1 y j)] with n hn he
  change freeAmplitude y j n=((4*Real.pi : ℂ)⁻¹) • TransversePlaneFields.field 1 y j n at he
  rw [he]
  change ⟪embedVector (n : Space),((4*Real.pi : ℂ)⁻¹) • TransversePlaneFields.field 1 y j n⟫=0
  rw [inner_smul_right,hn,mul_zero]

theorem vector_poloidal (a : PositiveIndex) :
    ComplexTransverseExpansion.vector (Sum.inl a)=(normalizer a.1 : ℂ) •
      realLift (VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩)) := by
  change realLift (normalizer a.1 • VectorHarmonicSeparation.lift
    (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩))=_
  rw [map_smul,Complex.coe_smul]

theorem vector_toroidal (a : PositiveIndex) :
    ComplexTransverseExpansion.vector (Sum.inr a)=(normalizer a.1 : ℂ) •
      realLift (VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩)) := by
  change realLift (normalizer a.1 • VectorHarmonicSeparation.lift
    (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩))=_
  rw [map_smul,Complex.coe_smul]

theorem mapped_poloidal (a : PositiveIndex) (y : Space) (i j : Fin 3) :
    SphereVectorComponents.coordinate i (⟪ComplexTransverseExpansion.vector (Sum.inl a),freeAmplitude y j⟫ •
      ComplexTransverseExpansion.vector (Sum.inl a))=
      (tmCoefficient a y j*SourceRadiation.phase (a.1+1)) •
        SphereVectorComponents.coordinate i (realLift (VectorHarmonicSeparation.lift
          (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩))) := by
  let c := ⟪ComplexTransverseExpansion.vector (Sum.inl a),freeAmplitude y j⟫
  change SphereVectorComponents.coordinate i (c • ComplexTransverseExpansion.vector (Sum.inl a))=_
  rw [map_smul,vector_poloidal,map_smul,smul_smul]
  have hc : c*(normalizer a.1 : ℂ)=tmCoefficient a y j*SourceRadiation.phase (a.1+1) := by
    rw [mul_comm]
    exact tm_source_coefficient a y j
  rw [hc]

theorem mapped_toroidal (a : PositiveIndex) (y : Space) (i j : Fin 3) :
    SphereVectorComponents.coordinate i (⟪ComplexTransverseExpansion.vector (Sum.inr a),freeAmplitude y j⟫ •
      ComplexTransverseExpansion.vector (Sum.inr a))=
      (teCoefficient a y j*(-SourceRadiation.phase (a.1+1))) •
        SphereVectorComponents.coordinate i (realLift (VectorHarmonicSeparation.lift
          (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩))) := by
  let c := ⟪ComplexTransverseExpansion.vector (Sum.inr a),freeAmplitude y j⟫
  change SphereVectorComponents.coordinate i (c • ComplexTransverseExpansion.vector (Sum.inr a))=_
  rw [map_smul,vector_toroidal,map_smul,smul_smul]
  have hc : c*(normalizer a.1 : ℂ)=teCoefficient a y j*(-SourceRadiation.phase (a.1+1)) := by
    rw [mul_comm]
    exact te_source_coefficient a y j
  rw [hc]

theorem Lp_expansion (y : Space) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => ContinuousMap.toLp 2 angularMeasure ℂ (farMap a y i j))
      (ContinuousMap.toLp 2 angularMeasure ℂ (freeMap y i j)) := by
  let f := fun a : PositiveIndex => SphereVectorComponents.coordinate i
    (⟪ComplexTransverseExpansion.vector (Sum.inl a),freeAmplitude y j⟫ • ComplexTransverseExpansion.vector (Sum.inl a))
  let g := fun a : PositiveIndex => SphereVectorComponents.coordinate i
    (⟪ComplexTransverseExpansion.vector (Sum.inr a),freeAmplitude y j⟫ • ComplexTransverseExpansion.vector (Sum.inr a))
  have h : HasSum (Sum.elim f g) (SphereVectorComponents.coordinate i (freeAmplitude y j)) := by
    convert (ComplexTransverseExpansion.expansion (freeAmplitude y j) (freeAmplitude_tangent y j)).mapL
      (SphereVectorComponents.coordinate i) using 1
    funext a
    cases a <;> rfl
  have hf : Summable f := by
    simpa only [Function.comp_def,Sum.elim_inl] using h.summable.comp_injective Sum.inl_injective
  have hg : Summable g := by
    simpa only [Function.comp_def,Sum.elim_inr] using h.summable.comp_injective Sum.inr_injective
  have he := (hf.hasSum.sum hg.hasSum).unique h
  rw [freeMap_toLp,← he]
  convert hf.hasSum.add hg.hasSum using 1
  funext a
  dsimp only [f,g]
  rw [mapped_poloidal,mapped_toroidal,farMap,map_add,map_smul,map_smul,
    realComponent_toLp,realComponent_toLp]

end OQ14.FreeFarFieldExpansion

#print axioms OQ14.FreeFarFieldExpansion.freeMap_toLp
#print axioms OQ14.FreeFarFieldExpansion.freeAmplitude_tangent
#print axioms OQ14.FreeFarFieldExpansion.vector_poloidal
#print axioms OQ14.FreeFarFieldExpansion.vector_toroidal
#print axioms OQ14.FreeFarFieldExpansion.mapped_poloidal
#print axioms OQ14.FreeFarFieldExpansion.mapped_toroidal
#print axioms OQ14.FreeFarFieldExpansion.Lp_expansion
