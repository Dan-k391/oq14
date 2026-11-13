import Packet07DrivenAxialHerglotz

/-! The actual magnetic Herglotz field is covariant under axial rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialHerglotzMagnetic
open Maxwell SphereHarmonicBasis SphereAngularSymmetry ModalAxialRotation
  Packet07DrivenAxialAngularVector Packet07DrivenAxialAngular Packet07DrivenAxialHerglotz
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def magneticMap (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := (WithLp.equiv 2 (Fin 3 → ℂ)).symm (AngularHerglotz.magneticAmplitude (fun n j => A n j) n)
  continuous_toFun := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
    apply continuous_pi
    intro i
    exact AngularHerglotz.magneticAmplitude_continuous (fun n j => A n j)
      (fun j => (EuclideanSpace.proj j).continuous.comp A.continuous) i

theorem magnetic_amplitude_rotate (θ : ℝ) (A : C(Sphere,Vector)) (n : Sphere) :
    AngularHerglotz.magneticAmplitude (fun n j => rotated θ A n j) n =
      ModalAxialRotation.vector θ (AngularHerglotz.magneticAmplitude (fun n j => A n j)
        (sphereMap (rotation (-θ)) n)) := by
  have ht : ((Real.cos θ : ℂ)^2+(Real.sin θ : ℂ)^2)=1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  ext i
  fin_cases i <;> simp [AngularHerglotz.magneticAmplitude,cross_apply,ConicalPlaneWaves.direction,
    rotated,pull,rotate,vector,sphereMap,rotation,spatial,Real.cos_neg,Real.sin_neg,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul]
  all_goals simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · have hh := congrArg (fun q : ℂ => q*((n : Space) 1 : ℂ)*A (sphereMap (rotation (-θ)) n) 2) ht
    dsimp only [sphereMap,rotation] at hh
    simp only [neg_neg] at hh
    linear_combination hh
  · have hh := congrArg (fun q : ℂ => -q*((n : Space) 0 : ℂ)*A (sphereMap (rotation (-θ)) n) 2) ht
    dsimp only [sphereMap,rotation] at hh
    simp only [neg_neg] at hh
    linear_combination hh
  · ring

theorem rotated_magneticMap (θ : ℝ) (A : C(Sphere,Vector)) :
    magneticMap (rotated θ A)=rotated θ (magneticMap A) := by
  ext n i
  change AngularHerglotz.magneticAmplitude (fun n j => rotated θ A n j) n i = _
  rw [magnetic_amplitude_rotate]
  rfl

theorem magnetic_covariant (θ k : ℝ) (A : C(Sphere,Vector)) (x : Space) (i : Fin 3) :
    AngularHerglotz.magnetic k (fun n j => rotated θ A n j) x i =
      ModalAxialRotation.vector θ (AngularHerglotz.magnetic k (fun n j => A n j) (rotation (-θ) x)) i := by
  change AngularHerglotz.electric k (fun n j => magneticMap (rotated θ A) n j) x i = _
  rw [rotated_magneticMap]
  exact electric_covariant θ k (magneticMap A) x i
end OQ14.Packet07DrivenAxialHerglotzMagnetic
#print axioms OQ14.Packet07DrivenAxialHerglotzMagnetic.magnetic_amplitude_rotate
#print axioms OQ14.Packet07DrivenAxialHerglotzMagnetic.rotated_magneticMap
#print axioms OQ14.Packet07DrivenAxialHerglotzMagnetic.magnetic_covariant
