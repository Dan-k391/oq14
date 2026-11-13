import Packet07DrivenCyclicAngularSmooth
import Packet07DrivenAxialHerglotzMagnetic

/-! Electric and magnetic Herglotz integrals under cyclic proper rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenCyclicHerglotz
open MeasureTheory Maxwell SphereHarmonicBasis SphereAngularSymmetry Packet06CyclicRotation
  Packet06CyclicRotationMaxwell Packet07DrivenCyclicAngularVector Packet07DrivenCyclicAngular
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

theorem wave_rotate (k : ℝ) (x : Space) (n : Sphere) :
    SphereReactionKernel.wave k x (sphereMap rotation n) = SphereReactionKernel.wave k (unrotate x) n := by
  have h := rotation.inner_map_map (rotation.symm x) (n : Space)
  rw [rotation.apply_symm_apply] at h
  have hp : @inner ℝ Space _ ((sphereMap rotation n) : Space) x = @inner ℝ Space _ (n : Space) (unrotate x) := by
    change @inner ℝ Space _ (rotation (n : Space)) x = _
    rw [real_inner_comm,h,real_inner_comm]
    rfl
  simp only [SphereReactionKernel.wave,hp]

theorem sphere_inverse (n : Sphere) : sphereMap rotation.symm (sphereMap rotation n)=n := by
  apply Subtype.ext
  exact rotation.symm_apply_apply n

theorem electric_covariant (k : ℝ) (A : C(Sphere,Vector)) (x : Space) (i : Fin 3) :
    AngularHerglotz.electric k (fun n j => rotated A n j) x i =
      rotateField (AngularHerglotz.electric k (fun n j => A n j)) x i := by
  have hrot := (measurePreserving_sphereMap rotation).integral_comp (sphereMap rotation).measurableEmbedding
    (fun n : Sphere => rotated A n i*SphereReactionKernel.wave (-k) x n)
  change (∫ n : Sphere, rotated A (sphereMap rotation n) i*SphereReactionKernel.wave (-k) x (sphereMap rotation n) ∂angularMeasure) =
    ∫ n : Sphere, rotated A n i*SphereReactionKernel.wave (-k) x n ∂angularMeasure at hrot
  unfold AngularHerglotz.electric SphereWaveCalculus.moment
  change (∫ n : Sphere, rotated A n i*SphereReactionKernel.wave (-k) x n ∂angularMeasure) = _
  rw [←hrot]
  have hv (n : Sphere) : rotated A (sphereMap rotation n) i = A n (WeakCurl.previous i) := by
    change Packet07DrivenCyclicAngularVector.rotate (A (sphereMap rotation.symm (sphereMap rotation n))) i = _
    rw [sphere_inverse]
    rfl
  simp only [hv,wave_rotate]
  rfl

theorem magnetic_amplitude_rotate (A : C(Sphere,Vector)) (n : Sphere) :
    AngularHerglotz.magneticAmplitude (fun n j => rotated A n j) n =
      fun i => AngularHerglotz.magneticAmplitude (fun n j => A n j) (sphereMap rotation.symm n) (WeakCurl.previous i) := by
  have h0 : rotation.symm (n : Space) 0 = n.val 1 := by change unrotate n 0 = _; simp [unrotate,WeakCurl.next]
  have h1 : rotation.symm (n : Space) 1 = n.val 2 := by change unrotate n 1 = _; simp [unrotate,WeakCurl.next]
  have h2 : rotation.symm (n : Space) 2 = n.val 0 := by change unrotate n 2 = _; simp [unrotate,WeakCurl.next]
  ext i
  fin_cases i <;> simp [AngularHerglotz.magneticAmplitude,cross_apply,ConicalPlaneWaves.direction,
    rotated,pull,Packet07DrivenCyclicAngularVector.rotate,sphereMap,WeakCurl.previous,h0,h1,h2]

theorem rotated_magneticMap (A : C(Sphere,Vector)) :
    Packet07DrivenAxialHerglotzMagnetic.magneticMap (rotated A)=
      rotated (Packet07DrivenAxialHerglotzMagnetic.magneticMap A) := by
  ext n i
  change AngularHerglotz.magneticAmplitude (fun n j => rotated A n j) n i = _
  rw [magnetic_amplitude_rotate]
  rfl

theorem magnetic_covariant (k : ℝ) (A : C(Sphere,Vector)) (x : Space) (i : Fin 3) :
    AngularHerglotz.magnetic k (fun n j => rotated A n j) x i =
      rotateField (AngularHerglotz.magnetic k (fun n j => A n j)) x i := by
  change AngularHerglotz.electric k (fun n j => Packet07DrivenAxialHerglotzMagnetic.magneticMap (rotated A) n j) x i = _
  rw [rotated_magneticMap]
  exact electric_covariant k (Packet07DrivenAxialHerglotzMagnetic.magneticMap A) x i
end OQ14.Packet07DrivenCyclicHerglotz
#print axioms OQ14.Packet07DrivenCyclicHerglotz.wave_rotate
#print axioms OQ14.Packet07DrivenCyclicHerglotz.sphere_inverse
#print axioms OQ14.Packet07DrivenCyclicHerglotz.electric_covariant
#print axioms OQ14.Packet07DrivenCyclicHerglotz.magnetic_amplitude_rotate
#print axioms OQ14.Packet07DrivenCyclicHerglotz.rotated_magneticMap
#print axioms OQ14.Packet07DrivenCyclicHerglotz.magnetic_covariant
