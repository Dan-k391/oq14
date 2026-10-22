import PolarMomentTesting

/-! Actual measurable bounded angular weights for conical radial projection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.ConicalMomentWeights
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1 OQ14.ConicalCapField
  OQ14.ConicalRadialDivergence OQ14.ConicalTangentialDivergence

def scalar (a d t : ℝ) (n : Sphere) : ℂ := (angularWeight a d t n : ℂ)

def radial (a d t : ℝ) (i : Fin 3) (n : Sphere) : ℂ := scalar a d t n*((n : Space) i : ℂ)

def tangent (a d t : ℝ) (i : Fin 3) (n : Sphere) : ℂ :=
  (CapSturmLiouville.coefficient d t ((n : Space) 2)*SphereCapH1.gradient a t n i : ℝ)

theorem unit_self (n : Sphere) : unit (n : Space)=n := by
  simpa only [one_smul] using unit_polar 1 zero_lt_one n

theorem scalar_unit (a d t : ℝ) (x : Space) : scalar a d t (unit x)=(spatialWeight a d t x : ℂ) := by
  simp only [scalar,angularWeight,spatialWeight,permittivity]

theorem scalar_sphere (a d t : ℝ) (n : Sphere) : scalar a d t n=(spatialWeight a d t n : ℂ) := by
  simp only [scalar,angularWeight,spatialWeight,permittivity,unit_self]

theorem tangent_unit (a d t : ℝ) (i : Fin 3) (x : Space) : tangent a d t i (unit x)=(weightedTangent a d t x i : ℂ) := by
  simp only [tangent,weightedTangent,permittivity,PiLp.smul_apply,smul_eq_mul]

theorem tangent_sphere (a d t : ℝ) (i : Fin 3) (n : Sphere) : tangent a d t i n=(weightedTangent a d t n i : ℂ) := by
  simp only [tangent,weightedTangent,permittivity,unit_self,PiLp.smul_apply,smul_eq_mul]

theorem norm_unit_coordinate (x : Space) (i : Fin 3) : ‖x‖*(unit x : Space) i=x i := by
  by_cases hx : x=0
  · subst x
    simp
  · simp only [unit,if_neg hx,PiLp.smul_apply,smul_eq_mul]
    rw [← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_mul]

theorem radial_product (a d t : ℝ) (i : Fin 3) (x : Space) :
    (‖x‖ : ℂ)*radial a d t i (unit x)=(spatialWeight a d t x*x i : ℝ) := by
  rw [radial,scalar_unit]
  have h := congrArg Complex.ofReal (norm_unit_coordinate x i)
  simp only [Complex.ofReal_mul] at h ⊢
  linear_combination (spatialWeight a d t x : ℂ)*h

theorem scalar_measurable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (scalar a d t) := by
  have he : scalar a d t=(fun n : Sphere => (spatialWeight a d t n : ℂ)) := funext (scalar_sphere a d t)
  rw [he]
  exact Complex.measurable_ofReal.comp ((weight_measurable a d t ha ht ht1).comp measurable_subtype_coe)

theorem radial_measurable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    Measurable (radial a d t i) :=
  (scalar_measurable a d t ha ht ht1).mul
    (Complex.measurable_ofReal.comp (ConicalAngularTrial.coordinate_continuous i).measurable)

theorem tangent_measurable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    Measurable (tangent a d t i) := by
  have hm : Measurable (fun n : Sphere => weightedTangent a d t n i) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.measurable.comp
    ((weightedTangent_measurable a d t ha ht ht1).comp measurable_subtype_coe)
  have he : tangent a d t i=(fun n : Sphere => (weightedTangent a d t n i : ℂ)) := funext (tangent_sphere a d t i)
  rw [he]
  exact Complex.measurable_ofReal.comp hm

theorem scalar_bound (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ n : Sphere, ‖scalar a d t n‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weight_bound a d t ha hd ht ht1
  refine ⟨C,hC,fun n => ?_⟩
  simpa only [scalar_sphere,Complex.norm_real] using hb n

theorem radial_bound (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    ∃ C ≥ (0 : ℝ), ∀ n : Sphere, ‖radial a d t i n‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := scalar_bound a d t ha hd ht ht1
  refine ⟨C,hC,fun n => ?_⟩
  have hn : ‖(n : Space) i‖ ≤ 1 := (PiLp.norm_apply_le (n : Space) i).trans_eq (sphere_norm n)
  rw [radial,norm_mul,Complex.norm_real]
  exact (mul_le_mul (hb n) hn (norm_nonneg _) hC).trans_eq (mul_one C)

theorem tangent_bound (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    ∃ C ≥ (0 : ℝ), ∀ n : Sphere, ‖tangent a d t i n‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := weightedTangent_bound a d t ha hd ht ht1
  refine ⟨C,hC,fun n => ?_⟩
  rw [tangent_sphere,Complex.norm_real]
  exact (PiLp.norm_apply_le _ i).trans (hb n)

end OQ14.ConicalMomentWeights

#print axioms OQ14.ConicalMomentWeights.unit_self
#print axioms OQ14.ConicalMomentWeights.scalar_unit
#print axioms OQ14.ConicalMomentWeights.scalar_sphere
#print axioms OQ14.ConicalMomentWeights.tangent_unit
#print axioms OQ14.ConicalMomentWeights.tangent_sphere
#print axioms OQ14.ConicalMomentWeights.norm_unit_coordinate
#print axioms OQ14.ConicalMomentWeights.radial_product
#print axioms OQ14.ConicalMomentWeights.scalar_measurable
#print axioms OQ14.ConicalMomentWeights.radial_measurable
#print axioms OQ14.ConicalMomentWeights.tangent_measurable
#print axioms OQ14.ConicalMomentWeights.scalar_bound
#print axioms OQ14.ConicalMomentWeights.radial_bound
#print axioms OQ14.ConicalMomentWeights.tangent_bound
