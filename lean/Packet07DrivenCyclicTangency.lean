import Packet07DrivenCyclicAngular

/-! Cyclic proper rotation preserves angular transversality. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenCyclicTangency
open Maxwell SphereHarmonicBasis SphereAngularSymmetry Packet06CyclicRotation Packet07DrivenCyclicAngularVector Packet07DrivenCyclicAngular
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

theorem normal_pair (n : Sphere) (v : Vector) :
    @inner ℂ Vector _ (TransversePlaneFields.normal n) (Packet07DrivenCyclicAngularVector.rotate v) =
      @inner ℂ Vector _ (TransversePlaneFields.normal (sphereMap rotation.symm n)) v := by
  have h0 : rotation.symm (n : Space) 0 = n.val 1 := by change unrotate n 0 = _; simp [unrotate,WeakCurl.next]
  have h1 : rotation.symm (n : Space) 1 = n.val 2 := by change unrotate n 1 = _; simp [unrotate,WeakCurl.next]
  have h2 : rotation.symm (n : Space) 2 = n.val 0 := by change unrotate n 2 = _; simp [unrotate,WeakCurl.next]
  simp only [PiLp.inner_apply,Fin.sum_univ_three,RCLike.inner_apply,TransversePlaneFields.normal,
    ComplexVectorSphere.embed_apply,Packet07DrivenCyclicAngularVector.rotate,WithLp.equiv_symm_pi_apply,
    Complex.conj_ofReal,conj_trivial]
  simp [sphereMap,WeakCurl.previous,h0,h1,h2]
  ring

theorem rotated_tangent (A : C(Sphere,Vector))
    (hA : ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (A n)=0) :
    ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (rotated A n)=0 := by
  intro n
  change @inner ℂ Vector _ (TransversePlaneFields.normal n) (Packet07DrivenCyclicAngularVector.rotate (A (sphereMap rotation.symm n)))=0
  rw [normal_pair]
  exact hA _
end OQ14.Packet07DrivenCyclicTangency
#print axioms OQ14.Packet07DrivenCyclicTangency.normal_pair
#print axioms OQ14.Packet07DrivenCyclicTangency.rotated_tangent
