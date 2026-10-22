import SphereParityMaxwell
import FiniteSphereIncident
import NewtonStripMaxwell
import ParityMaterialField

/-! Literal density-integrated parity fields and the continuous strip representative of the material total field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityPlaneFields
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open SphereReactionKernel (reaction entryBound entryBound_nonnegative)
open SphereMagneticParity (magneticReaction)
open Maxwell (Field)
open scoped Topology
abbrev Space := FourierL2.Space

def electric (e : Bool) (k : ℝ) (ρ : Source) : Field :=
  fun x i => ∑ j : Fin 3, ∫ y, reaction e k x y i j*ρ j y

def magnetic (e : Bool) (k : ℝ) (ρ : Source) : Field :=
  fun x i => ∑ j : Fin 3, ∫ y, magneticReaction e k x y i j*ρ j y

theorem electric_integrand (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i j : Fin 3) : Integrable (fun y => reaction e k x y i j*ρ j y) :=
  (hρ j).bdd_mul' ((SphereReactionKernel.reaction_continuous e k i j).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => SphereReactionKernel.reaction_bound e k x y i j))

theorem magnetic_integrand (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i j : Fin 3) : Integrable (fun y => magneticReaction e k x y i j*ρ j y) := by
  have hc : Continuous (fun y => magneticReaction e k x y i j) := by
    unfold magneticReaction
    exact continuous_const.mul (((SphereMagneticKernel.K_continuous k i j).comp (continuous_const.sub continuous_id)).sub
      (continuous_const.mul ((SphereMagneticKernel.K_continuous k i j).comp (continuous_const.sub continuous_id))))
  exact (hρ j).bdd_mul' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => SphereMagneticParity.magnetic_bound e k x y i j))

private theorem field_bound (F : Fin 3 → Space → ℂ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hi : ∀ j, Integrable (fun y => F j y*ρ j y)) (C : ℝ) (hb : ∀ j y, ‖F j y‖ ≤ C) :
    ‖∑ j : Fin 3, ∫ y, F j y*ρ j y‖ ≤ C*sourceMass ρ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ∫ y, ‖F j y*ρ j y‖ := Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm _)
    _ ≤ ∑ j : Fin 3, C*(∫ y, ‖ρ j y‖) := Finset.sum_le_sum (fun j _ => by
      rw [← integral_const_mul]
      apply integral_mono_ae (hi j).norm ((hρ j).norm.const_mul C)
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb j y) (norm_nonneg _))
    _ = _ := by unfold sourceMass; rw [Finset.mul_sum]

theorem electric_bound (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) : ‖electric e k ρ x i‖ ≤ entryBound k*sourceMass ρ :=
  field_bound _ ρ hρ (fun j => electric_integrand e k ρ hρ x i j) _
    (fun j y => SphereReactionKernel.reaction_bound e k x y i j)

theorem magnetic_bound (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) : ‖magnetic e k ρ x i‖ ≤ entryBound k*sourceMass ρ :=
  field_bound _ ρ hρ (fun j => magnetic_integrand e k ρ hρ x i j) _
    (fun j y => SphereMagneticParity.magnetic_bound e k x y i j)

theorem electric_continuous (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (i : Fin 3) : Continuous (fun x => electric e k ρ x i) := by
  apply continuous_finset_sum
  intro j _
  apply continuous_of_dominated
    (fun x => (electric_integrand e k ρ hρ x i j).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (SphereReactionKernel.reaction_bound e k x y i j) (norm_nonneg _)))
    ((hρ j).norm.const_mul (entryBound k))
  filter_upwards with y
  exact ((SphereReactionKernel.reaction_continuous e k i j).comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem magnetic_continuous (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (i : Fin 3) : Continuous (fun x => magnetic e k ρ x i) := by
  apply continuous_finset_sum
  intro j _
  apply continuous_of_dominated
    (fun x => (magnetic_integrand e k ρ hρ x i j).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (SphereMagneticParity.magnetic_bound e k x y i j) (norm_nonneg _)))
    ((hρ j).norm.const_mul (entryBound k))
  filter_upwards with y
  exact (continuous_iff_continuousAt.mpr (fun x =>
    (SphereParityMaxwell.magnetic_differentiable e k x y i j).continuousAt)).mul continuous_const

private theorem sign_tangent (i : Fin 3) (hi : i ≠ 2) : SphereReactionKernel.sign i=1 := by
  simp [SphereReactionKernel.sign,hi]

theorem electric_true_zero (k : ℝ) (ρ : Source) (x : Space) (hx : x 2=0)
    (i : Fin 3) (hi : i ≠ 2) : electric true k ρ x i=0 := by
  unfold electric
  apply Finset.sum_eq_zero
  intro j _
  have he (y : Space) : reaction true k x y i j=0 := by
    rw [SphereMagneticParity.reaction_on_plane true k x y hx i j,sign_tangent i hi]
    norm_num
  simp only [he,zero_mul,integral_zero]

theorem magnetic_false_zero (k : ℝ) (ρ : Source) (x : Space) (hx : x 2=0)
    (i : Fin 3) (hi : i ≠ 2) : magnetic false k ρ x i=0 := by
  unfold magnetic
  apply Finset.sum_eq_zero
  intro j _
  have he (y : Space) : magneticReaction false k x y i j=0 := by
    rw [SphereMagneticParity.magnetic_on_plane false k x y hx i j,sign_tangent i hi]
    norm_num
  simp only [he,zero_mul,integral_zero]

def totalElectric (k B : ℝ) (ρ : Source) (incident : Field) : Field :=
  fun x i => incident x i+ExteriorContinuity.electric k ρ x i+
    ((B^2-1 : ℝ) : ℂ)*electric true k ρ x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*electric false k ρ x i

def totalMagnetic (k B : ℝ) (ρ : Source) (incident : Field) : Field :=
  fun x i => incident x i+MagneticResponse.magnetic k ρ x i+
    ((B^2-1 : ℝ) : ℂ)*magnetic true k ρ x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*magnetic false k ρ x i

theorem electric_material (c : StaticCoefficient.Coefficient) (k : ℝ)
    (u : VectorFourier.VectorL2) (e : Bool) :
    electric e k (DynamicVolume.source c u)=ParityMaterialField.reaction c e k u := rfl

theorem total_electric_continuousOn (k B d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : ∀ j, Integrable (ρ j)) (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|)
    (incident : Field) (hi : ∀ i, Continuous (fun x => incident x i)) (i : Fin 3) :
    ContinuousOn (fun x => totalElectric k B ρ incident x i) (NewtonSeparatedResponse.strip d) :=
  (((hi i).continuousOn.add (NewtonStripMaxwell.electric_continuousOn k ρ hρ d hd hh i)).add
    (continuous_const.mul (electric_continuous true k ρ hρ i)).continuousOn).add
      (continuous_const.mul (electric_continuous false k ρ hρ i)).continuousOn

theorem total_magnetic_continuousOn (k B d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : ∀ j, Integrable (ρ j)) (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|)
    (incident : Field) (hi : ∀ i, Continuous (fun x => incident x i)) (i : Fin 3) :
    ContinuousOn (fun x => totalMagnetic k B ρ incident x i) (NewtonSeparatedResponse.strip d) :=
  (((hi i).continuousOn.add (NewtonStripMaxwell.magnetic_continuousOn k ρ hρ d hd hh i)).add
    (continuous_const.mul (magnetic_continuous true k ρ hρ i)).continuousOn).add
      (continuous_const.mul (magnetic_continuous false k ρ hρ i)).continuousOn

theorem material_total_ae_strip (c : StaticCoefficient.Coefficient) (k B R d : ℝ)
    (hd : 0 < d) (u : VectorFourier.VectorL2) (incident : Field)
    (hc : ∀ y : Space, y ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap y)=0)
    (hh : ∀ j y, DynamicVolume.source c u j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ NewtonSeparatedResponse.strip d →
      ParityMaterialField.total c k B u incident x i=
        totalElectric k B (DynamicVolume.source c u) incident x i := by
  have he := NewtonStripMaxwell.electric_ae_strip k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (StaticNewton.material_source_ae c u) d R hd (DynamicVolume.source_zero c u R hc) hh i
  filter_upwards [he] with x hx hs
  unfold ParityMaterialField.total ParityMaterialField.scattered MaterialField.scattered totalElectric
  rw [hx hs]
  simp only [electric_material]
  ring

end OQ14.ParityPlaneFields
#print axioms OQ14.ParityPlaneFields.electric_integrand
#print axioms OQ14.ParityPlaneFields.magnetic_integrand
#print axioms OQ14.ParityPlaneFields.electric_bound
#print axioms OQ14.ParityPlaneFields.magnetic_bound
#print axioms OQ14.ParityPlaneFields.electric_continuous
#print axioms OQ14.ParityPlaneFields.magnetic_continuous
#print axioms OQ14.ParityPlaneFields.electric_true_zero
#print axioms OQ14.ParityPlaneFields.magnetic_false_zero
#print axioms OQ14.ParityPlaneFields.electric_material
#print axioms OQ14.ParityPlaneFields.total_electric_continuousOn
#print axioms OQ14.ParityPlaneFields.total_magnetic_continuousOn
#print axioms OQ14.ParityPlaneFields.material_total_ae_strip
