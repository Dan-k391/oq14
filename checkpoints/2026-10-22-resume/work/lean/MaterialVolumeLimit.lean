import MaterialStrongLimit
import DynamicStaticLimit

/-! Actual strong material-volume inverse convergence under bounded AE coefficient convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.MaterialVolumeLimit
open MeasureTheory Filter OQ14.StaticCoefficient OQ14.MaterialStrongLimit
open scoped Topology

def commonRadius (D R : ℝ) : ℝ := (2*(1+252*D*R^2))⁻¹

theorem commonRadius_positive (D R : ℝ) (hD : 0 ≤ D) : 0 < commonRadius D R := by
  dsimp only [commonRadius]
  positivity

theorem commonRadius_le (c : Coefficient) (D R : ℝ) (hb : c.bound ≤ D) :
    commonRadius D R ≤ DynamicStaticLimit.frequencyRadius c R := by
  have hs := DynamicStaticLimit.size_nonnegative c R
  have hC : 252*c.bound*R^2 ≤ 252*D*R^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (sq_nonneg R)
  have hd : 0 < 2*(1+252*c.bound*R^2) := by
    dsimp only [DynamicStaticLimit.size] at hs
    linarith
  simpa only [commonRadius,DynamicStaticLimit.frequencyRadius,DynamicStaticLimit.size,one_div] using
    one_div_le_one_div_of_le hd (show 2*(1+252*c.bound*R^2) ≤ 2*(1+252*D*R^2) by linarith)

theorem volumeBlock_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D k R : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x))) (f : VectorL2) :
    Tendsto (fun n => DynamicVolume.volumeBlock (c n) k R f) atTop (𝓝 (DynamicVolume.volumeBlock c₀ k R f)) := by
  have hin := sqrtMultiplier_tendsto c c₀ D hb hb₀ ha f
  have hP := VectorFourier.physicalProjection.continuous.tendsto _ |>.comp hin
  have hQ := (DynamicConvolution.operator k (2*R)).continuous.tendsto _ |>.comp hin
  have hSP := sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha _ _ hP
  have hSQ := sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha _ _ hQ
  have hconst : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
  simpa only [DynamicVolume.volumeBlock,StaticNewton.volumeBlock_eq,StaticCoefficient.weightedBlock,
    DynamicVolume.weightedRemainder,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.comp_apply] using (hconst.add hSP).sub hSQ

theorem inverse_apply_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D k R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hk : |k| ≤ commonRadius D R) (f : ℕ → VectorL2) (f₀ : VectorL2) (hf : Tendsto f atTop (𝓝 f₀)) :
    Tendsto (fun n => Ring.inverse (DynamicVolume.volumeBlock (c n) k R) (f n)) atTop
      (𝓝 (Ring.inverse (DynamicVolume.volumeBlock c₀ k R) f₀)) := by
  let A : ℕ → VectorL2 →L[ℂ] VectorL2 := fun n => DynamicVolume.volumeBlock (c n) k R
  let A₀ : VectorL2 →L[ℂ] VectorL2 := DynamicVolume.volumeBlock c₀ k R
  let u := Ring.inverse A₀ f₀
  have hkn (n : ℕ) := hk.trans (commonRadius_le (c n) D R (hb n))
  have hk₀ := hk.trans (commonRadius_le c₀ D R hb₀)
  have hun (n : ℕ) : IsUnit (A n) := DynamicVolume.volumeBlock_isUnit (c n) k R hR (by
    have he := DynamicStaticLimit.error_small (c n) k R (hkn n)
    linarith)
  have hu₀ : IsUnit A₀ := DynamicVolume.volumeBlock_isUnit c₀ k R hR (by
    have he := DynamicStaticLimit.error_small c₀ k R hk₀
    linarith)
  have hAu : A₀ u=f₀ := by
    have he := congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T f₀) (Ring.mul_inverse_cancel A₀ hu₀)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using he
  have hAn : Tendsto (fun n => A n u) atTop (𝓝 f₀) := by
    have hh := volumeBlock_tendsto c c₀ D k R hb hb₀ ha u
    change Tendsto (fun n => A n u) atTop (𝓝 (A₀ u)) at hh
    rwa [hAu] at hh
  have hres : Tendsto (fun n => f n-A n u) atTop (𝓝 0) := by simpa only [sub_self] using hf.sub hAn
  have hbound (n : ℕ) : ‖Ring.inverse (A n) (f n)-u‖ ≤ 2*‖f n-A n u‖ := by
    have hcancel : Ring.inverse (A n) (A n u)=u := by
      have he := congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T u) (Ring.inverse_mul_cancel (A n) (hun n))
      simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using he
    have heq : Ring.inverse (A n) (f n)-u=Ring.inverse (A n) (f n-A n u) := by rw [map_sub,hcancel]
    rw [heq]
    exact ((Ring.inverse (A n)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (DynamicStaticLimit.inverse_norm_two (c n) k R hR (hkn n)) (norm_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hl : Tendsto (fun n => 2*‖f n-A n u‖) atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using tendsto_const_nhds.mul hres.norm
  exact squeeze_zero (fun n => norm_nonneg _) hbound hl

def weightedSolution (c : Coefficient) (k R : ℝ) (incident : VectorL2) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock c k R) (sqrtMultiplier c incident)

def volumeField (c : Coefficient) (k R : ℝ) (incident : VectorL2) : VectorL2 :=
  incident+(NewtonL2.newtonOperator+DynamicConvolution.operator k (2*R))
    (sqrtMultiplier c (weightedSolution c k R incident))

theorem weightedSolution_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D k R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hk : |k| ≤ commonRadius D R) (incident : VectorL2) :
    Tendsto (fun n => weightedSolution (c n) k R incident) atTop (𝓝 (weightedSolution c₀ k R incident)) :=
  inverse_apply_tendsto c c₀ D k R hR hb hb₀ ha hk _ _ (sqrtMultiplier_tendsto c c₀ D hb hb₀ ha incident)

theorem volumeField_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D k R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hk : |k| ≤ commonRadius D R) (incident : VectorL2) :
    Tendsto (fun n => volumeField (c n) k R incident) atTop (𝓝 (volumeField c₀ k R incident)) := by
  have hu := weightedSolution_tendsto c c₀ D k R hR hb hb₀ ha hk incident
  have hs := sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha _ _ hu
  exact tendsto_const_nhds.add (((NewtonL2.newtonOperator+DynamicConvolution.operator k (2*R)).continuous.tendsto _).comp hs)

theorem volumeField_weighted (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius c R) (incident : VectorL2) :
    sqrtMultiplier c (volumeField c k R incident)=weightedSolution c k R incident := by
  have hu : IsUnit (DynamicVolume.volumeBlock c k R) := DynamicVolume.volumeBlock_isUnit c k R hR (by
    have he := DynamicStaticLimit.error_small c k R hk
    linarith)
  have he := congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T (sqrtMultiplier c incident))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c k R) hu)
  have heq : weightedSolution c k R incident-
      sqrtMultiplier c (NewtonL2.newtonOperator (sqrtMultiplier c (weightedSolution c k R incident)))-
      sqrtMultiplier c (DynamicConvolution.operator k (2*R) (sqrtMultiplier c (weightedSolution c k R incident)))=
      sqrtMultiplier c incident := by
    simpa only [DynamicVolume.volumeBlock,StaticNewton.volumeBlock,StaticNewton.response,
      DynamicVolume.weightedRemainder,ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply,ContinuousLinearMap.comp_apply,weightedSolution] using he
  simp only [volumeField,map_add,ContinuousLinearMap.add_apply]
  rw [← heq]
  abel

theorem volumeField_material_source (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius c R) (incident : VectorL2) :
    sqrtMultiplier c (weightedSolution c k R incident) =ᵐ[volume]
      fun x => (c.value x : ℂ) • volumeField c k R incident x := by
  have h := sqrtMultiplier_square_ae c (volumeField c k R incident)
  rwa [volumeField_weighted c k R hR hk incident] at h

end OQ14.MaterialVolumeLimit


#print axioms OQ14.MaterialVolumeLimit.commonRadius_positive
#print axioms OQ14.MaterialVolumeLimit.commonRadius_le
#print axioms OQ14.MaterialVolumeLimit.volumeBlock_tendsto
#print axioms OQ14.MaterialVolumeLimit.inverse_apply_tendsto
#print axioms OQ14.MaterialVolumeLimit.weightedSolution_tendsto
#print axioms OQ14.MaterialVolumeLimit.volumeField_tendsto
#print axioms OQ14.MaterialVolumeLimit.volumeField_weighted
#print axioms OQ14.MaterialVolumeLimit.volumeField_material_source
