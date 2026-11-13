import Packet06SphereLocalField
import ModalOverlapAngular

/-! The actual sphere mode has a nonvanishing limiting tangential projection
at every on-axis center where its axial component is nonzero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet06SphereProjection
open MeasureTheory Metric Set Filter Maxwell AngularPower
open scoped Topology

def tangent (q : Sphere) (i : Fin 3) : ℂ :=
  ((basis 2 - ((q : Space) 2) • (q : Space)) i : ℝ)

def average (F : Field) (c : Space) (r : ℝ) : ℂ :=
  ∫ q : Sphere, ∑ i : Fin 3, F (c + r • (q : Space)) i * tangent q i ∂angularMeasure

theorem average_continuous (F : Field) (hF : ∀ i, Continuous (fun x => F x i)) (c : Space) :
    Continuous (average F c) := by
  have ht (i : Fin 3) : Continuous (fun q : Sphere => tangent q i) := by
    simp only [tangent,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      Complex.ofReal_sub,Complex.ofReal_mul]
    exact continuous_const.sub ((Complex.continuous_ofReal.comp
      (ConicalAngularTrial.coordinate_continuous 2)).mul
      (Complex.continuous_ofReal.comp (ConicalAngularTrial.coordinate_continuous i)))
  have h : Continuous (fun p : ℝ × Sphere =>
      ∑ i : Fin 3, F (c + p.1 • (p.2 : Space)) i * tangent p.2 i) := by
    apply continuous_finset_sum
    intro i _
    exact ((hF i).comp (continuous_const.add (continuous_fst.smul
      (continuous_subtype_val.comp continuous_snd)))).mul ((ht i).comp continuous_snd)
  simpa only [Measure.restrict_univ,average] using
    continuous_parametric_integral_of_continuous h isCompact_univ

theorem average_zero (F : Field) (c : Space) (h0 : F c 0 = 0) (h1 : F c 1 = 0) :
    average F c 0 = (2/3 : ℂ)*ModalOverlapAngular.area*F c 2 := by
  unfold average
  simp only [zero_smul,add_zero,Fin.sum_univ_three,h0,h1,zero_mul,zero_add]
  have he : (fun q : Sphere => F c 2*tangent q 2) =
      fun q => F c 2 + (-F c 2)*(ConicalAngularTrial.coordinate 2 q : ℂ)^2 := by
    funext q
    simp only [tangent,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      basis,EuclideanSpace.single_apply,ite_true,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,ConicalAngularTrial.coordinate]
    ring
  rw [he,ModalOverlapAngular.integral_affine_square]
  ring

theorem sphere_average_near_center (n : ℝ) (z w : ℂ) (c : Space)
    (hc0 : c 0 = 0) (hc1 : c 1 = 0)
    (hne : Packet06SphereLocalField.inner n z w c 2 ≠ 0) :
    let A := (2/3 : ℂ)*ModalOverlapAngular.area*Packet06SphereLocalField.inner n z w c 2
    A ≠ 0 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, |r| < R →
      ‖average (Packet06SphereLocalField.inner n z w) c r-A‖ < ‖A‖/2 := by
  dsimp only
  let F := Packet06SphereLocalField.inner n z w
  let A := (2/3 : ℂ)*ModalOverlapAngular.area*F c 2
  have hA : A ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ModalOverlapAngular.area_ne_zero) hne
  have h0 : F c 0=0 := by
    simp [F,Packet06SphereLocalField.inner,ModalOrigin.centerE,ModalDipole.axisField,hc0]
  have h1 : F c 1=0 := by
    simp [F,Packet06SphereLocalField.inner,ModalOrigin.centerE,ModalDipole.axisField,hc1]
  have hF (i : Fin 3) : Continuous (fun x => F x i) :=
    continuous_const.mul (ModalOrigin.centerE_continuous ((n : ℂ)*z) i)
  have hv : average F c 0=A := average_zero F c h0 h1
  have ht : Tendsto (average F c) (𝓝 0) (𝓝 A) := by
    rw [← hv]
    exact (average_continuous F hF c).continuousAt
  have he := ht.eventually (Metric.ball_mem_nhds A (half_pos (norm_pos_iff.mpr hA)))
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨hA,R,hR,?_⟩
  intro r hr
  have hh := hball (show dist r 0 < R by simpa [Real.dist_eq] using hr)
  simpa only [mem_ball,dist_eq_norm] using hh

end OQ14.Packet06SphereProjection
#print axioms OQ14.Packet06SphereProjection.average_continuous
#print axioms OQ14.Packet06SphereProjection.average_zero
#print axioms OQ14.Packet06SphereProjection.sphere_average_near_center
