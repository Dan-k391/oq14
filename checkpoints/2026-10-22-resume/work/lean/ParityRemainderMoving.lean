import ParityRemainderBound
import SourceHerglotzMoving
import ReactionGainError

/-! Genuine gained total-reaction plane flux tends to zero for electric-wall finite incidence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityRemainderMoving
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation
open ParityRemainderBound
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def upper (k b R T γ Ci Cp M A₀ a : ℝ) : ℝ :=
  ((b^2+1)*M^2)*(SourceHerglotzWhole.electricConstant k R T (γ*a)*a^2)+
    ((1+1/b^2)*Ci*M*A₀)*a+
    ((1+1/b^2)*M^2)*(SourceHerglotzWhole.magneticConstant k R T (γ*a)*a^4)+
    ((1+1/b^2)*(b^2+1)*Cp*M^2)*a^2

theorem budget_bound (k b R T γ Ci Cp M A₀ a m w : ℝ)
    (hR : 0 ≤ R) (hT : 0 < T) (hγ : 0 < γ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hdM : γ*a ≤ T+R) (hCi : 0 ≤ Ci) (hCp : 0 ≤ Cp) (hM : 0 ≤ M)
    (hm0 : 0 ≤ m) (hw0 : 0 ≤ w) (hm : m ≤ M*a^2) (hw : w ≤ A₀/a) :
    budget k (b/a) R T (γ*a) Ci Cp m w ≤ upper k b R T γ Ci Cp M A₀ a := by
  have hE := SourceHerglotzMoving.electric_nonnegative k R T (γ*a) hR hT (mul_pos hγ ha)
  have hH := SourceHerglotzMoving.magnetic_nonnegative k R T (γ*a) hR hT (mul_pos hγ ha) hdM
  have hge := ReactionGainError.gain_bound b a ha ha1
  have hgm := ReactionGainError.inverse_gain_bound b a ha.le ha1
  calc
    _ ≤ ((b^2+1)/a^2)*SourceHerglotzWhole.electricConstant k R T (γ*a)*(M*a^2)^2+
      (1+1/b^2)*Ci*(M*a^2)*(A₀/a)+
      (1+1/b^2)*SourceHerglotzWhole.magneticConstant k R T (γ*a)*(M*a^2)^2+
      (1+1/b^2)*((b^2+1)/a^2)*Cp*(M*a^2)^2 := by
      unfold budget
      gcongr
    _ = _ := by unfold upper; field_simp; ring

theorem upper_limit (k b R T γ Ci Cp M A₀ : ℝ) (hγ : γ ≠ 0) (hTR : T+R ≠ 0) :
    Tendsto (upper k b R T γ Ci Cp M A₀) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h2 : Tendsto (fun a : ℝ => a^2) (𝓝[>] 0) (𝓝 0) := by simpa using h1.pow 2
  have he := (SourceHerglotzScaling.electric_scaled_limit k R T γ hγ).const_mul ((b^2+1)*M^2)
  have hm := ((SourceHerglotzScaling.magnetic_scaled_limit k R T γ hTR hγ).mul h2).const_mul ((1+1/b^2)*M^2)
  have hh := ((he.add (h1.const_mul ((1+1/b^2)*Ci*M*A₀))).add hm).add
    (h2.const_mul ((1+1/b^2)*(b^2+1)*Cp*M^2))
  convert hh using 1
  · funext a
    unfold upper
    ring
  · simp

theorem total_minus_free_convergence (k b R T γ M A₀ : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hγ : 0 < γ) (hM : 0 ≤ M)
    (ρ : ℝ → Source) (p : ℝ → ι → Space) (j : ℝ → ι → Fin 3) (A : ℝ → ι → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hp : ∀ᶠ a in 𝓝[>] 0, ∀ s, p a s ∈ closedBall 0 R)
    (hm : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a) ≤ M*a^2)
    (hA : ∀ᶠ a in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a) :
    Tendsto (fun a => ∫ q : Plane, ‖ParityTotalFlux.totalFlux k (b/a) (ρ a) (p a) (j a) (A a) q-
      ParityTotalFlux.freeFlux k (ρ a) (p a) (j a) (A a) q‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Ci,Cp,hCi,hCp,hh⟩ := whole_bounds (ι := ι) k R hR hk
  have hpos : 0 < T+R := by linarith
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ≤ 1 ∧ γ*a ≤ T+R := by
    have ht : Tendsto (fun a : ℝ => γ*a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((show Continuous (fun a : ℝ => γ*a) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have ha : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    filter_upwards [ha,ht.eventually (gt_mem_nhds hpos)] with a ha ht
    exact ⟨ha.le,ht.le⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _
    (upper_limit k b R T γ Ci Cp M A₀ hγ.ne' hpos.ne')
  filter_upwards [hρ,hp,hm,hA,hsmall,self_mem_nhdsWithin] with a hρ hp hm hA hs ha
  have heq (q : Plane) : ParityTotalFlux.totalFlux k (b/a) (ρ a) (p a) (j a) (A a) q-
      ParityTotalFlux.freeFlux k (ρ a) (p a) (j a) (A a) q=
      ParityTotalFlux.remainder k (b/a) (ρ a) (p a) (j a) (A a) q := by
    rw [ParityTotalFlux.total_identity]
    ring
  simp_rw [heq]
  exact ((hh (b/a) T (γ*a) (mul_pos hγ ha) hT hTR hs.2 (ρ a) hρ (p a) (j a) (A a) hp).2.2).trans
    (budget_bound k b R T γ Ci Cp M A₀ a _ _ hR (by linarith) hγ ha hs.1 hs.2 hCi hCp hM
      (sourceMass_nonnegative _) (Finset.sum_nonneg (fun s _ => norm_nonneg _)) hm hA)

end OQ14.ParityRemainderMoving
#print axioms OQ14.ParityRemainderMoving.budget_bound
#print axioms OQ14.ParityRemainderMoving.upper_limit
#print axioms OQ14.ParityRemainderMoving.total_minus_free_convergence
