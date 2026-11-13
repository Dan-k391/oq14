import Packet06ConeProfilePositive
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeZeroRoot
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereCapH1 OQ14.SphereCapWeak
  OQ14.AngularPower OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

theorem zero_contrast_root_unique (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) (hroot : determinant 0 t a = 0) : a = 2 := by
  have ht : 0 < t := by linarith
  let F : Sphere → ℝ := fun q => field a t q * ((q : Space) 2)
  have hpos : 0 < ∫ q : Sphere, F q ∂angularMeasure :=
    Packet06ConeProfilePositive.profile_axis_pair_positive a t ha ht0 ht1
  have hgrad := (field_hasWeakTangentialGradient a t ha ht ht1).2 2 (fun _ : Space => (1 : ℝ)) contDiff_const
  have hgrad' : (∫ q : Sphere, (gradient a t q) 2 ∂angularMeasure) =
      2 * ∫ q : Sphere, F q ∂angularMeasure := by
    simp only [fderiv_const,Pi.zero_apply,ContinuousLinearMap.zero_apply,mul_one,sub_zero,zero_sub] at hgrad
    have he : (fun q : Sphere => field a t q * -(2 * (q : Space) 2)) = fun q => -(2 * F q) := by
      funext q
      dsimp [F]
      ring
    rw [he,integral_neg,integral_const_mul,neg_neg] at hgrad
    exact hgrad
  have hweak := field_weighted_weak a 0 t ha ht ht1 hroot (fun x : Space => x 2)
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff)
  have hweak' : (∫ q : Sphere, (gradient a t q) 2 ∂angularMeasure) =
      a * ∫ q : Sphere, F q ∂angularMeasure := by
    have he : (fun x : Space => x 2) = (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) := rfl
    rw [he] at hweak
    simpa only [CapSturmLiouville.coefficient,add_zero,ite_self,one_mul,
      ContinuousLinearMap.fderiv,F] using hweak
  rw [hgrad'] at hweak'
  nlinarith
#print axioms OQ14.Packet06ConeZeroRoot.zero_contrast_root_unique
end OQ14.Packet06ConeZeroRoot
