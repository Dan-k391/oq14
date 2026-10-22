import SourceHerglotzScaling

/-! Genuine moving-gap source/Herglotz coherent error convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzMoving
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation SourceHerglotzLocal SourceHerglotzWhole
open scoped ComplexConjugate Topology

theorem electric_nonnegative (k R T d : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (hd : 0 < d) :
    0 ≤ electricConstant k R T d := by
  unfold electricConstant tailConstant PlaneMaxwellLocal.electricCoefficient PlaneMaxwellLocal.remainderCoefficient
    PointMaxwellTail.tailConstant MaxwellPlaneTail.electricErrorConstant MaxwellPlaneTail.magneticErrorConstant
    MaxwellPlaneTail.leadingConstant PlaneInverseCube.diskConstant SphereReactionKernel.entryBound SphereReactionKernel.surfaceMass
  positivity

theorem magnetic_nonnegative (k R T d : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (hd : 0 < d) (hdM : d ≤ T+R) :
    0 ≤ magneticConstant k R T d := by
  have hM : 0 ≤ T+R := (hd.trans_le hdM).le
  have hl : 0 ≤ Real.log ((T+R)/d) := Real.log_nonneg ((one_le_div hd).mpr hdM)
  unfold magneticConstant tailConstant PlaneMaxwellSharp.gradientMass PointMaxwellTail.tailConstant
    MaxwellPlaneTail.electricErrorConstant MaxwellPlaneTail.magneticErrorConstant MaxwellPlaneTail.leadingConstant
    PlaneInverseCube.diskConstant SphereReactionKernel.entryBound SphereReactionKernel.surfaceMass
  positivity

private theorem weighted_bound (D M e w C A a : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hw : 0 ≤ w) (hA : 0 ≤ A) (hC : M ≤ C*a^3) (he : e ≤ D*M) (hamp : w ≤ A/a) :
    w*e ≤ (C*A)*(D*a^2) := by
  calc
    _ ≤ w*(D*M) := mul_le_mul_of_nonneg_left he hw
    _ ≤ (A/a)*(D*M) := mul_le_mul_of_nonneg_right hamp (mul_nonneg hD hM)
    _ ≤ (A/a)*(D*(C*a^3)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hC hD) (div_nonneg hA ha.le)
    _ = _ := by field_simp; ring

theorem electric_bound (k R T γ C A a : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ) (ha : 0 < a)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA : 0 ≤ A)
    (ρ σ : Source) (hρ : Admissible R (γ*a) ρ) (hσ : Admissible R (γ*a) σ)
    (z : FourierL2.Space) (hz : z ∈ closedBall 0 R) (m : Fin 3) (c : ℂ)
    (hc : ‖c‖ ≤ A/a) (he : sourceMass (ρ-σ) ≤ C*a^3) :
    (∫ q : Plane, ‖conj c*(electricFlux k ρ z m q-electricFlux k σ z m q)‖) ≤
      (C*A)*(electricConstant k R T (γ*a)*a^2) := by
  simp only [norm_mul, Complex.norm_conj, integral_const_mul]
  exact weighted_bound _ _ _ _ C A a ha (electric_nonnegative k R T (γ*a) hR (by linarith) (mul_pos hγ ha))
    (sourceMass_nonnegative _) (norm_nonneg _) hA he
    (SourceHerglotzWhole.electric_sub_mass k R T (γ*a) hR (mul_pos hγ ha) hk hT hTR ρ σ hρ hσ z hz m).2 hc

theorem magnetic_bound (k R T γ C A a : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ) (ha : 0 < a)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA : 0 ≤ A) (hdM : γ*a ≤ T+R)
    (ρ σ : Source) (hρ : Admissible R (γ*a) ρ) (hσ : Admissible R (γ*a) σ)
    (z : FourierL2.Space) (hz : z ∈ closedBall 0 R) (j : Fin 3) (c : ℂ)
    (hc : ‖c‖ ≤ A/a) (he : sourceMass (ρ-σ) ≤ C*a^3) :
    (∫ q : Plane, ‖c*(magneticFlux k ρ z j q-magneticFlux k σ z j q)‖) ≤
      (C*A)*(magneticConstant k R T (γ*a)*a^2) := by
  simp only [norm_mul, integral_const_mul]
  exact weighted_bound _ _ _ _ C A a ha (magnetic_nonnegative k R T (γ*a) hR (by linarith) (mul_pos hγ ha) hdM)
    (sourceMass_nonnegative _) (norm_nonneg _) hA he
    (SourceHerglotzWhole.magnetic_sub_mass k R T (γ*a) hR (mul_pos hγ ha) hk hT hTR hdM ρ σ hρ hσ z hz j).2 hc

theorem electric_convergence (k R T γ C A : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA : 0 ≤ A)
    (ρ σ : ℝ → Source) (z : ℝ → FourierL2.Space) (m : ℝ → Fin 3) (c : ℝ → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hz : ∀ᶠ a in 𝓝[>] 0, z a ∈ closedBall 0 R)
    (hc : ∀ᶠ a in 𝓝[>] 0, ‖c a‖ ≤ A/a)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3) :
    Tendsto (fun a => ∫ q : Plane,
      ‖conj (c a)*(electricFlux k (ρ a) (z a) (m a) q-electricFlux k (σ a) (z a) (m a) q)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := (SourceHerglotzScaling.electric_scaled_limit k R T γ hγ.ne').const_mul (C*A)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hz,hc,he,self_mem_nhdsWithin] with a hρ hσ hz hc he ha
  exact electric_bound k R T γ C A a hR hγ ha hk hT hTR hA _ _ hρ hσ _ hz _ _ hc he

theorem magnetic_convergence (k R T γ C A : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA : 0 ≤ A)
    (ρ σ : ℝ → Source) (z : ℝ → FourierL2.Space) (j : ℝ → Fin 3) (c : ℝ → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hz : ∀ᶠ a in 𝓝[>] 0, z a ∈ closedBall 0 R)
    (hc : ∀ᶠ a in 𝓝[>] 0, ‖c a‖ ≤ A/a)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3) :
    Tendsto (fun a => ∫ q : Plane,
      ‖c a*(magneticFlux k (ρ a) (z a) (j a) q-magneticFlux k (σ a) (z a) (j a) q)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 < T+R := by linarith
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a ≤ T+R := by
    have ht : Tendsto (fun a : ℝ => γ*a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((show Continuous (fun a : ℝ => γ*a) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact (ht.eventually (gt_mem_nhds hM)).mono (fun a ha => ha.le)
  have ht := (SourceHerglotzScaling.magnetic_scaled_limit k R T γ hM.ne' hγ.ne').const_mul (C*A)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hz,hc,he,hsmall,self_mem_nhdsWithin] with a hρ hσ hz hc he hs ha
  exact magnetic_bound k R T γ C A a hR hγ ha hk hT hTR hA hs _ _ hρ hσ _ hz _ _ hc he

end OQ14.SourceHerglotzMoving
#print axioms OQ14.SourceHerglotzMoving.electric_nonnegative
#print axioms OQ14.SourceHerglotzMoving.magnetic_nonnegative
#print axioms OQ14.SourceHerglotzMoving.electric_bound
#print axioms OQ14.SourceHerglotzMoving.magnetic_bound
#print axioms OQ14.SourceHerglotzMoving.electric_convergence
#print axioms OQ14.SourceHerglotzMoving.magnetic_convergence
