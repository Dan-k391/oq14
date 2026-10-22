import PlaneQuadraticFlux

/-! Genuine quadratic Maxwell flux stability at a shrinking plane gap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PlaneQuadraticMoving
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation PlaneQuadraticFlux
open scoped Topology

private def polynomial (k R T γ a : ℝ) : ℝ :=
  (4*|k| *(4*Real.pi)⁻¹*PlaneMaxwellLocal.electricCoefficient k R T*(Real.pi+PlaneInverseCube.diskConstant))*
    (|k|/γ^2*a^3+(1/γ^3)*a^2)+
    (MaxwellPlaneTail.tailConstant k R*PlaneInverseCube.diskConstant/T)*a^5

theorem scaled_identity (k R T γ a : ℝ) (hγ : γ ≠ 0) (ha : a ≠ 0) :
    wholeConstant k R T (γ*a)*a^5=polynomial k R T γ a := by
  unfold wholeConstant diskConstant magneticCoefficient polynomial
  field_simp
  ring

theorem scaled_limit (k R T γ : ℝ) (hγ : γ ≠ 0) :
    Tendsto (fun a => wholeConstant k R T (γ*a)*a^5) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (polynomial k R T γ) := by unfold polynomial; fun_prop
  have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hzero : polynomial k R T γ 0=0 := by simp [polynomial]
  rw [hzero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (scaled_identity k R T γ a hγ (ne_of_gt ha)).symm

theorem self_difference_bound (k R T γ C M a : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ) (ha : 0 < a)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ρ σ : Source) (hρ : Admissible R (γ*a) ρ) (hσ : Admissible R (γ*a) σ)
    (hmρ : sourceMass ρ ≤ M*a^2) (hmσ : sourceMass σ ≤ M*a^2)
    (he : sourceMass (ρ-σ) ≤ C*a^3) :
    (∫ q : Plane, ‖MaxwellPlaneL1.flux k ρ ρ q-MaxwellPlaneL1.flux k σ σ q‖) ≤
      (2*C*M)*(wholeConstant k R T (γ*a)*a^5) := by
  have hD := whole_constant_nonnegative k R T (γ*a) hR (by linarith) (mul_pos hγ ha)
  calc
    _ ≤ wholeConstant k R T (γ*a)*(sourceMass (ρ-σ)*sourceMass ρ+sourceMass σ*sourceMass (ρ-σ)) :=
      difference_mass k R T (γ*a) hR (mul_pos hγ ha) hT hTR ρ ρ σ σ hρ hρ hσ hσ
    _ ≤ wholeConstant k R T (γ*a)*((C*a^3)*(M*a^2)+(M*a^2)*(C*a^3)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact add_le_add (mul_le_mul he hmρ (sourceMass_nonnegative _) (by positivity))
        (mul_le_mul hmσ he (sourceMass_nonnegative _) (by positivity))
    _ = _ := by ring

theorem self_difference_convergence (k R T γ C M : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ρ σ : ℝ → Source)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hmρ : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a) ≤ M*a^2)
    (hmσ : ∀ᶠ a in 𝓝[>] 0, sourceMass (σ a) ≤ M*a^2)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3) :
    Tendsto (fun a => ∫ q : Plane, ‖MaxwellPlaneL1.flux k (ρ a) (ρ a) q-
      MaxwellPlaneL1.flux k (σ a) (σ a) q‖) (𝓝[>] 0) (𝓝 0) := by
  have ht := (scaled_limit k R T γ hγ.ne').const_mul (2*C*M)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hmρ,hmσ,he,self_mem_nhdsWithin] with a hρ hσ hmρ hmσ he ha
  exact self_difference_bound k R T γ C M a hR hγ ha hT hTR hC hM _ _ hρ hσ hmρ hmσ he

end OQ14.PlaneQuadraticMoving
#print axioms OQ14.PlaneQuadraticMoving.scaled_identity
#print axioms OQ14.PlaneQuadraticMoving.scaled_limit
#print axioms OQ14.PlaneQuadraticMoving.self_difference_bound
#print axioms OQ14.PlaneQuadraticMoving.self_difference_convergence
