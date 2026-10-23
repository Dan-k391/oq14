import RestrictedTEPlaneLocal
import RegularTEMagneticBounds

/-! Actual finite-band TE magnetic tails, uniform over the angular sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEMagneticTail
open Complex Filter Set Metric Maxwell DebyeRadialTrace HarmonicPolynomial
open SymmetricHarmonicJets RestrictedTEIncoming
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

theorem ray_bounds (A : Index →₀ ℂ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop,
    ∀ n : Sphere,
      (∀ i : Fin 3, ‖RestrictedTEPlaneLocal.magnetic A (r • (n : Space)) i‖≤C/r) ∧
      ‖dot (position n) (RestrictedTEPlaneLocal.magnetic A (r • (n : Space)))‖≤C/r^2 := by
  classical
  have hb (q : Index) := RegularTEMagneticBounds.regular_ray_bounds q.val.1 (polynomial q)
    (EvenHarmonicProjection.homogeneous _ _ q.property.1)
    (EvenHarmonicProjection.harmonic _ _ q.property.2)
  choose C hC hB using hb
  let D := ∑ q ∈ A.support, ‖coefficient A q‖*C q
  have hD : 0≤D := Finset.sum_nonneg (fun q _ => mul_nonneg (norm_nonneg _) (hC q))
  refine ⟨D,hD,?_⟩
  have he := (Finset.eventually_all A.support).2 (fun q _ => hB q)
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  intro n
  have hsum (i : Fin 3) : RestrictedTEPlaneLocal.magnetic A (r • (n : Space)) i=
      ∑ q ∈ A.support, coefficient A q*
        DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (r • (n : Space)) i :=
    magnetic_sum A _ i
  constructor
  · intro i
    rw [hsum]
    calc
      _ ≤ ∑ q ∈ A.support, ‖coefficient A q*
          DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (r • (n : Space)) i‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ A.support, ‖coefficient A q‖*(C q/r) := Finset.sum_le_sum (fun q hq => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hr q hq n).1 i) (norm_nonneg _))
      _ = _ := by simp only [D,Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring
  · have hdot : dot (position n) (RestrictedTEPlaneLocal.magnetic A (r • (n : Space)))=
        ∑ q ∈ A.support, coefficient A q*dot (position n)
          (DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (r • (n : Space))) := by
      unfold dot
      simp only [hsum,Finset.mul_sum,← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hdot]
    calc
      _ ≤ ∑ q ∈ A.support, ‖coefficient A q*dot (position n)
          (DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (r • (n : Space)))‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ A.support, ‖coefficient A q‖*(C q/r^2) := Finset.sum_le_sum (fun q hq => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hr q hq n).2 (norm_nonneg _))
      _ = _ := by simp only [D,Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring

theorem field_bounds (A : Index →₀ ℂ) : ∃ C : ℝ, 0≤C ∧ ∃ T : ℝ, 2≤T ∧
    ∀ x : Space, T<‖x‖ →
      (∀ i : Fin 3, ‖RestrictedTEPlaneLocal.magnetic A x i‖≤C/‖x‖) ∧
      ‖dot (MaxwellRadiation.direction x) (RestrictedTEPlaneLocal.magnetic A x)‖≤C/‖x‖^2 := by
  obtain ⟨C,hC,hb⟩ := ray_bounds A
  obtain ⟨T,hT⟩ := eventually_atTop.1 hb
  refine ⟨C,hC,max 2 T,le_max_left _ _,?_⟩
  intro x hx
  have hr : 0<‖x‖ := by linarith [le_max_left (2 : ℝ) T]
  let n : Sphere := ⟨‖x‖⁻¹ • x,by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne']⟩
  have he : ‖x‖ • (n : Space)=x := by
    change ‖x‖ • (‖x‖⁻¹ • x)=x
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hd : position n=MaxwellRadiation.direction x := by
    ext i
    simp [position,n,MaxwellRadiation.direction,GreenKernel.unitCoordinate,PiLp.smul_apply,div_eq_mul_inv]
    ring
  simpa only [he,hd] using hT ‖x‖ (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx)) n

end OQ14.RestrictedTEMagneticTail
#print axioms OQ14.RestrictedTEMagneticTail.ray_bounds
#print axioms OQ14.RestrictedTEMagneticTail.field_bounds
