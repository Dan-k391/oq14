import Packet07DrivenAxialAngular

/-! Axial angular rotation preserves literal transverse polarization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenAxialTangency
open Maxwell SphereHarmonicBasis SphereAngularSymmetry ModalAxialRotation Packet07DrivenAxialAngularVector Packet07DrivenAxialAngular
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

theorem normal_pair (θ : ℝ) (n : Sphere) (v : Vector) :
    @inner ℂ Vector _ (TransversePlaneFields.normal n) (rotate θ v) =
      @inner ℂ Vector _ (TransversePlaneFields.normal (sphereMap (rotation (-θ)) n)) v := by
  simp only [PiLp.inner_apply,Fin.sum_univ_three,RCLike.inner_apply,TransversePlaneFields.normal,
    ComplexVectorSphere.embed_apply,rotate,WithLp.equiv_symm_pi_apply,vector,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def,Complex.conj_ofReal,conj_trivial]
  simp [sphereMap,rotation,spatial,Real.cos_neg,Real.sin_neg,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
  ring

theorem rotated_tangent (θ : ℝ) (A : C(Sphere,Vector))
    (hA : ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (A n)=0) :
    ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (rotated θ A n)=0 := by
  intro n
  change @inner ℂ Vector _ (TransversePlaneFields.normal n) (rotate θ (A (sphereMap (rotation (-θ)) n)))=0
  rw [normal_pair]
  exact hA _
end OQ14.Packet07DrivenAxialTangency
#print axioms OQ14.Packet07DrivenAxialTangency.normal_pair
#print axioms OQ14.Packet07DrivenAxialTangency.rotated_tangent
