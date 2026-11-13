import Packet07DrivenAxialAngularSmooth
import AngularHerglotz

/-! The actual electric Herglotz integral commutes with axial rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialHerglotz
open MeasureTheory Maxwell SphereHarmonicBasis SphereAngularSymmetry ModalAxialRotation
  Packet07DrivenAxialAngularVector Packet07DrivenAxialAngular
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

theorem wave_rotate (θ k : ℝ) (x : Space) (n : Sphere) :
    SphereReactionKernel.wave k x (sphereMap (rotation θ) n) =
      SphereReactionKernel.wave k (rotation (-θ) x) n := by
  have h := (rotation θ).inner_map_map (rotation (-θ) x) (n : Space)
  have he : rotation θ (rotation (-θ) x)=x := by
    change spatial θ (spatial (-θ) x)=x
    simpa using spatial_inverse (-θ) x
  rw [he] at h
  have hp : @inner ℝ Space _ ((sphereMap (rotation θ) n) : Space) x =
      @inner ℝ Space _ (n : Space) (rotation (-θ) x) := by
    change @inner ℝ Space _ (rotation θ (n : Space)) x = _
    rw [real_inner_comm,h,real_inner_comm]
  simp only [SphereReactionKernel.wave,hp]

theorem sphere_rotate_inverse (θ : ℝ) (n : Sphere) :
    sphereMap (rotation (-θ)) (sphereMap (rotation θ) n)=n := by
  apply Subtype.ext
  change rotation (-θ) (rotation θ (n : Space))=n
  exact spatial_inverse θ n

theorem electric_covariant (θ k : ℝ) (A : C(Sphere,Vector)) (x : Space) (i : Fin 3) :
    AngularHerglotz.electric k (fun n j => rotated θ A n j) x i =
      ModalAxialRotation.vector θ (AngularHerglotz.electric k (fun n j => A n j) (rotation (-θ) x)) i := by
  have hI (j : Fin 3) : Integrable (fun n : Sphere => A n j*SphereReactionKernel.wave (-k) (rotation (-θ) x) n) angularMeasure := by
    apply Continuous.integrable_of_hasCompactSupport
    · have hA : Continuous (fun n : Sphere => A n j) := (EuclideanSpace.proj j).continuous.comp A.continuous
      exact hA.mul (by unfold SphereReactionKernel.wave; fun_prop)
    · exact HasCompactSupport.of_compactSpace _
  have hrot := (measurePreserving_sphereMap (rotation θ)).integral_comp
    (sphereMap (rotation θ)).measurableEmbedding
    (fun n : Sphere => rotated θ A n i*SphereReactionKernel.wave (-k) x n)
  change (∫ n : Sphere, rotated θ A (sphereMap (rotation θ) n) i*SphereReactionKernel.wave (-k) x (sphereMap (rotation θ) n) ∂angularMeasure) =
    ∫ n : Sphere, rotated θ A n i*SphereReactionKernel.wave (-k) x n ∂angularMeasure at hrot
  unfold AngularHerglotz.electric SphereWaveCalculus.moment
  change (∫ n : Sphere, rotated θ A n i*SphereReactionKernel.wave (-k) x n ∂angularMeasure) =
    ModalAxialRotation.vector θ (fun j => ∫ n : Sphere, A n j*SphereReactionKernel.wave (-k) (rotation (-θ) x) n ∂angularMeasure) i
  rw [←hrot]
  have hv (n : Sphere) : rotated θ A (sphereMap (rotation θ) n) i = ModalAxialRotation.vector θ (fun j => A n j) i := by
    change rotate θ (A (sphereMap (rotation (-θ)) (sphereMap (rotation θ) n))) i = _
    rw [sphere_rotate_inverse]
    rfl
  simp only [hv,wave_rotate]
  fin_cases i
  · change (∫ n : Sphere, ((Real.cos θ : ℂ)*A n 0-(Real.sin θ : ℂ)*A n 1)*
      SphereReactionKernel.wave (-k) (rotation (-θ) x) n ∂angularMeasure) = _
    simp only [sub_mul,mul_assoc]
    rw [integral_sub ((hI 0).const_mul _) ((hI 1).const_mul _),integral_const_mul,integral_const_mul]
    rfl
  · change (∫ n : Sphere, ((Real.sin θ : ℂ)*A n 0+(Real.cos θ : ℂ)*A n 1)*
      SphereReactionKernel.wave (-k) (rotation (-θ) x) n ∂angularMeasure) = _
    simp only [add_mul,mul_assoc]
    rw [integral_add ((hI 0).const_mul _) ((hI 1).const_mul _),integral_const_mul,integral_const_mul]
    rfl
  · rfl

end OQ14.Packet07DrivenAxialHerglotz
#print axioms OQ14.Packet07DrivenAxialHerglotz.wave_rotate
#print axioms OQ14.Packet07DrivenAxialHerglotz.sphere_rotate_inverse
#print axioms OQ14.Packet07DrivenAxialHerglotz.electric_covariant
