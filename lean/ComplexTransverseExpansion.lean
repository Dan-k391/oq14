import ComplexVectorSphere

/-! Actual complex transverse vector expansion and rank-one inner product series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ComplexTransverseExpansion
open MeasureTheory OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open OQ14.VectorHarmonicNormalization
open scoped ComplexInnerProductSpace
abbrev ModeIndex := PositiveIndex ⊕ PositiveIndex

def vector (a : ModeIndex) : ComplexVectorSphere.Ambient := realLift (polarized a)

theorem vector_orthonormal : Orthonormal ℂ vector := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [vector,vector,realLift_inner,orthonormal_iff_ite.mp polarized_orthonormal]
  split_ifs <;> simp

theorem coefficient (a : ModeIndex) (F : ComplexVectorSphere.Ambient) :
    ⟪vector a,F⟫=((@inner ℝ _ _ (polarized a) (realPart F) : ℝ) : ℂ)+
      Complex.I*((@inner ℝ _ _ (polarized a) (imagPart F) : ℝ) : ℂ) := by
  conv_lhs => rw [real_imag_decomposition F]
  rw [inner_add_right,inner_smul_right]
  simp only [vector,realLift_inner]

theorem expansion (F : ComplexVectorSphere.Ambient) (hF : IsTangential F) :
    HasSum (fun a : ModeIndex => ⟪vector a,F⟫ • vector a) F := by
  let r : TransverseHarmonicBasis.transverseSpace :=
    ⟨realPart F,TransverseHarmonicBasis.tangential_mem _ (realPart_tangent F hF)⟩
  let s : TransverseHarmonicBasis.transverseSpace :=
    ⟨imagPart F,TransverseHarmonicBasis.tangential_mem _ (imagPart_tangent F hF)⟩
  let L : TransverseHarmonicBasis.transverseSpace →L[ℝ] ComplexVectorSphere.Ambient :=
    realLift.comp TransverseHarmonicBasis.transverseSpace.subtypeL
  have hr := (TransverseHarmonicBasis.expansion r).mapL L
  have hs := (TransverseHarmonicBasis.expansion s).mapL L
  have ht := hr.add (hs.const_smul Complex.I)
  convert ht using 1
  · funext a
    rw [coefficient]
    simp only [add_smul,mul_smul,L,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_smul,Submodule.subtype_apply,Submodule.coe_smul]
    rfl
  · exact real_imag_decomposition F

theorem inner_series (F G : ComplexVectorSphere.Ambient) (hG : IsTangential G) :
    HasSum (fun a : ModeIndex => ⟪F,vector a⟫*⟪vector a,G⟫) ⟪F,G⟫ := by
  convert (expansion G hG).mapL (innerSL ℂ F) using 1
  funext a
  simp only [innerSL_apply,inner_smul_right,mul_comm]

end OQ14.ComplexTransverseExpansion

#print axioms OQ14.ComplexTransverseExpansion.vector_orthonormal
#print axioms OQ14.ComplexTransverseExpansion.coefficient
#print axioms OQ14.ComplexTransverseExpansion.expansion
#print axioms OQ14.ComplexTransverseExpansion.inner_series
