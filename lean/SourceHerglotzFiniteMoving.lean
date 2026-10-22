import SourceHerglotzFinite
import SourceHerglotzMoving
import FiniteSphereMaxwell

/-! Actual moving-gap coherent errors against finite genuine parity Herglotz illuminations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzFiniteMoving
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation SourceHerglotzFinite
open scoped Topology
variable {ι : Type*} [Fintype ι]
abbrev Space := FourierL2.Space

private theorem error_bound (D M e w C A a : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hm : M ≤ C*a^3) (he : e ≤ D*M*w) (hw : w ≤ A/a) :
    e ≤ (C*A)*(D*a^2) := by
  calc
    _ ≤ D*M*w := he
    _ ≤ (D*M)*(A/a) := mul_le_mul_of_nonneg_left hw (mul_nonneg hD hM)
    _ ≤ (D*(C*a^3))*(A/a) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm hD) (div_nonneg hA ha.le)
    _ = _ := by field_simp; ring

theorem electric_bound (k R T γ C A₀ a : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ) (ha : 0 < a)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (ρ σ : Source) (hρ : Admissible R (γ*a) ρ) (hσ : Admissible R (γ*a) σ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (hp : ∀ s, p s ∈ closedBall 0 R) (hA : (∑ s, ‖A s‖) ≤ A₀/a)
    (he : sourceMass (ρ-σ) ≤ C*a^3) :
    (∫ q : Plane, ‖electricMixed k ρ e p j A q-electricMixed k σ e p j A q‖) ≤
      (C*A₀)*(SourceHerglotzWhole.electricConstant k R T (γ*a)*a^2) :=
  error_bound _ _ _ _ C A₀ a ha
    (SourceHerglotzMoving.electric_nonnegative k R T (γ*a) hR (by linarith) (mul_pos hγ ha))
    (sourceMass_nonnegative _) hA₀ he
    (SourceHerglotzFinite.electric_sub_mass k R T (γ*a) hR (mul_pos hγ ha) hk hT hTR ρ σ hρ hσ e p j A hp).2 hA

theorem magnetic_bound (k R T γ C A₀ a : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ) (ha : 0 < a)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀) (hdM : γ*a ≤ T+R)
    (ρ σ : Source) (hρ : Admissible R (γ*a) ρ) (hσ : Admissible R (γ*a) σ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (hp : ∀ s, p s ∈ closedBall 0 R) (hA : (∑ s, ‖A s‖) ≤ A₀/a)
    (he : sourceMass (ρ-σ) ≤ C*a^3) :
    (∫ q : Plane, ‖magneticMixed k ρ e p j A q-magneticMixed k σ e p j A q‖) ≤
      (C*A₀)*(SourceHerglotzWhole.magneticConstant k R T (γ*a)*a^2) :=
  error_bound _ _ _ _ C A₀ a ha
    (SourceHerglotzMoving.magnetic_nonnegative k R T (γ*a) hR (by linarith) (mul_pos hγ ha) hdM)
    (sourceMass_nonnegative _) hA₀ he
    (SourceHerglotzFinite.magnetic_sub_mass k R T (γ*a) hR (mul_pos hγ ha) hk hT hTR hdM ρ σ hρ hσ e p j A hp).2 hA

theorem electric_convergence (k R T γ C A₀ : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (ρ σ : ℝ → Source) (e : ℝ → ι → Bool) (p : ℝ → ι → Space)
    (j : ℝ → ι → Fin 3) (A : ℝ → ι → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hp : ∀ᶠ a in 𝓝[>] 0, ∀ s, p a s ∈ closedBall 0 R)
    (hA : ∀ᶠ a in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3) :
    Tendsto (fun a => ∫ q : Plane,
      ‖electricMixed k (ρ a) (e a) (p a) (j a) (A a) q-electricMixed k (σ a) (e a) (p a) (j a) (A a) q‖)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := (SourceHerglotzScaling.electric_scaled_limit k R T γ hγ.ne').const_mul (C*A₀)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hp,hA,he,self_mem_nhdsWithin] with a hρ hσ hp hA he ha
  exact electric_bound k R T γ C A₀ a hR hγ ha hk hT hTR hA₀ _ _ hρ hσ _ _ _ _ hp hA he

theorem magnetic_convergence (k R T γ C A₀ : ℝ) (hR : 0 ≤ R) (hγ : 0 < γ)
    (hk : k ≠ 0) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (ρ σ : ℝ → Source) (e : ℝ → ι → Bool) (p : ℝ → ι → Space)
    (j : ℝ → ι → Fin 3) (A : ℝ → ι → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hp : ∀ᶠ a in 𝓝[>] 0, ∀ s, p a s ∈ closedBall 0 R)
    (hA : ∀ᶠ a in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3) :
    Tendsto (fun a => ∫ q : Plane,
      ‖magneticMixed k (ρ a) (e a) (p a) (j a) (A a) q-magneticMixed k (σ a) (e a) (p a) (j a) (A a) q‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 < T+R := by linarith
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a ≤ T+R := by
    have ht : Tendsto (fun a : ℝ => γ*a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((show Continuous (fun a : ℝ => γ*a) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact (ht.eventually (gt_mem_nhds hM)).mono (fun a ha => ha.le)
  have ht := (SourceHerglotzScaling.magnetic_scaled_limit k R T γ hM.ne' hγ.ne').const_mul (C*A₀)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hp,hA,he,hsmall,self_mem_nhdsWithin] with a hρ hσ hp hA he hs ha
  exact magnetic_bound k R T γ C A₀ a hR hγ ha hk hT hTR hA₀ hs _ _ hρ hσ _ _ _ _ hp hA he

end OQ14.SourceHerglotzFiniteMoving
#print axioms OQ14.SourceHerglotzFiniteMoving.electric_bound
#print axioms OQ14.SourceHerglotzFiniteMoving.magnetic_bound
#print axioms OQ14.SourceHerglotzFiniteMoving.electric_convergence
#print axioms OQ14.SourceHerglotzFiniteMoving.magnetic_convergence
