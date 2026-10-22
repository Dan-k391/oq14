import HomogeneousEuler
import ConicalStaticDivergence

/-! Actual weighted homogeneous displacement and its weak Euler and Gauss identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalDisplacement
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
open scoped Topology

def displacement (ν a d t : ℝ) (x : Space) : Space := permittivity d t x • electric ν a t x

def angularDisplacement (ν a d t : ℝ) (n : Sphere) : Space :=
  CapSturmLiouville.coefficient d t ((n : Space) 2) • angularElectric ν a t n

theorem component_locallyIntegrable (ν a d t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    LocallyIntegrable (fun x => displacement ν a d t x i) := by
  let f : Space → ℝ := fun x => electric ν a t x i
  have hf := ConicalSpatialTests.electric_component_locallyIntegrable ν a t hν ha ht ht1 i
  let S : Set Space := {x | t < |(unit x : Space) 2|}
  have hm : Measurable (fun x : Space => (unit x : Space) 2) :=
    (ConicalAngularTrial.coordinate_continuous 2).measurable.comp unit_measurable
  have hS : MeasurableSet S := measurableSet_lt measurable_const (continuous_abs.measurable.comp hm)
  have he : (fun x => displacement ν a d t x i)=f+d • S.indicator f := by
    funext x
    simp only [displacement,PiLp.smul_apply,smul_eq_mul]
    by_cases hx : x ∈ S
    · have hx' : t < |(unit x : Space) 2| := hx
      simp only [permittivity,CapSturmLiouville.coefficient,if_neg (not_le.mpr hx'),
        Pi.add_apply,Pi.smul_apply,indicator_of_mem hx,smul_eq_mul,f]
      ring
    · have hx' : |(unit x : Space) 2| ≤ t := le_of_not_gt hx
      simp only [permittivity,CapSturmLiouville.coefficient,if_pos hx',
        Pi.add_apply,Pi.smul_apply,indicator_of_not_mem hx,smul_eq_mul,mul_zero,add_zero,one_mul,f]
  rw [he]
  exact hf.add ((hf.indicator hS).smul d)

theorem angular_component_integrable (ν a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    Integrable (fun n : Sphere => angularDisplacement ν a d t n i) angularMeasure := by
  obtain ⟨C,_,hC⟩ := angular_bounds ν a t ha ht ht1
  have hm : Measurable (fun n : Sphere => angularElectric ν a t n i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.measurable.comp
      (angularElectric_measurable ν a t ha ht ht1)
  have hi : Integrable (fun n : Sphere => angularElectric ν a t n i) angularMeasure :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun n => (PiLp.norm_apply_le _ i).trans (hC n).2))
  simpa only [angularDisplacement,PiLp.smul_apply,smul_eq_mul] using
    SphereCapWeak.coefficient_integrable _ hi d t

theorem displacement_polar (ν a d t r : ℝ) (hr : 0 < r) (n : Sphere) :
    displacement ν a d t (r • (n : Space))=r^(ν-1) • angularDisplacement ν a d t n := by
  rw [displacement,permittivity_polar d t r hr n,electric_polar ν a t r hr n,
    angularDisplacement,smul_comm]

theorem component_weak_euler (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, displacement ν a d t x i*fderiv ℝ ψ x x)=
      -(ν+2)*(∫ x : Space, displacement ν a d t x i*ψ x) := by
  apply HomogeneousEuler.weak_euler ν hν _ (component_locallyIntegrable ν a d t hν.le ha ht ht1 i)
    _ (angular_component_integrable ν a d t ha ht ht1 i) _ ψ hψ hc
  intro r hr n
  rw [displacement_polar ν a d t r hr n]
  simp only [PiLp.smul_apply,smul_eq_mul]

theorem weak_gauss (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1)=a) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, fderiv ℝ ψ x (displacement ν a d t x))=0 := by
  simpa only [displacement,map_smul,smul_eq_mul] using
    ConicalStaticDivergence.weak_divergence ν a d t hν ha ht ht1 hroot heq ψ hψ hc

end OQ14.ConicalDisplacement

#print axioms OQ14.ConicalDisplacement.component_locallyIntegrable
#print axioms OQ14.ConicalDisplacement.angular_component_integrable
#print axioms OQ14.ConicalDisplacement.displacement_polar
#print axioms OQ14.ConicalDisplacement.component_weak_euler
#print axioms OQ14.ConicalDisplacement.weak_gauss
