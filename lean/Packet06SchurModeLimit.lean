import Packet06SchurPersistence
import Mathlib.Topology.UniformSpace.UniformApproximation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurModeLimit
open Filter Metric Set Packet06RankOneRepair Packet06ScalarSchur Packet06SchurAnalytic
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem convergent_kernel_modes (A : ℕ → ℂ → E →L[ℂ] E) (A₀ : ℂ → E →L[ℂ] E)
    (u₀ w : E) (ψ : E →L[ℂ] ℂ) (z₀ : ℂ) (d : ℂ)
    (hA : TendstoLocallyUniformlyOn A A₀ atTop univ)
    (hA₀ : Differentiable ℂ A₀) (hAn : ∀ᶠ n in atTop, Differentiable ℂ (A n))
    (hunit : IsUnit (repair (A₀ z₀) w ψ)) (hAu : A₀ z₀ u₀ = 0) (hψ : ψ u₀ = 1)
    (hder : HasDerivAt (fun z => scalar (A₀ z) w ψ) d z₀) (hd : d ≠ 0) :
    ∃ z : ℕ → ℂ, Tendsto z atTop (𝓝 z₀) ∧
      Tendsto (fun n => Ring.inverse (repair (A n (z n)) w ψ) w) atTop (𝓝 u₀) ∧
      ∀ᶠ n in atTop,
        let un := Ring.inverse (repair (A n (z n)) w ψ) w
        un ≠ 0 ∧ A n (z n) un = 0 ∧ ψ un = 1 ∧
        (∀ x, A n (z n) x = 0 ↔ x = ψ x • un) ∧
        (ψ (Ring.inverse (repair (A n (z n)) w ψ) ((deriv (A n) (z n)) un))) ≠ 0 := by
  have hzero : scalar (A₀ z₀) w ψ = 0 := scalar_zero _ _ _ _ hunit hAu hψ
  obtain ⟨z,hz,hroots⟩ := Packet06SchurPersistence.simple_schur_persistence
    A A₀ w ψ z₀ d hA hA₀ hAn hunit hzero hder hd
  obtain ⟨r,hr,hbase,hunitn,hinv,_⟩ :=
    Packet06RepairLimit.locally_uniform_repairs A A₀ w ψ z₀ hA hA₀.continuous hunit
  let U := ball z₀ r
  have hzU : z₀ ∈ U := mem_ball_self hr
  have hzball : ∀ᶠ n in atTop, z n ∈ U := hz.eventually (isOpen_ball.mem_nhds hzU)
  have hwithin : Tendsto z atTop (𝓝[U] z₀) := tendsto_nhdsWithin_iff.mpr ⟨hz,hzball⟩
  have hcont : ContinuousWithinAt (fun v => Ring.inverse (repair (A₀ v) w ψ)) U z₀ := by
    have hC : AnalyticAt ℂ (fun v => repair (A₀ v) w ψ) z₀ :=
      (hA₀.analyticAt z₀).add analyticAt_const
    exact ((analyticOnNhd_inverse (𝕜 := ℂ) _ hunit).comp
      (f := fun v : ℂ => repair (A₀ v) w ψ) hC).continuousAt.continuousWithinAt
  have hinvt := hinv.tendsto_comp hcont hzU hwithin
  have hvec := (ContinuousLinearMap.apply ℂ E w).continuous.tendsto _ |>.comp hinvt
  have hcenter : Ring.inverse (repair (A₀ z₀) w ψ) w = u₀ :=
    repaired_inverse_vector _ u₀ w ψ hunit hAu hψ
  refine ⟨z,hz,?_,?_⟩
  · simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, hcenter] using hvec
  · filter_upwards [hroots,hunitn,hzball,hAn] with n hn hunitn hnU hdiff
    have hu := hunitn (z n) hnU
    have hcross := scalar_hasDerivAt (A n) (deriv (A n) (z n)) w ψ (z n)
      (hdiff (z n)).hasDerivAt hu
    have hn2 := hn.2.1
    rw [hcross.deriv] at hn2
    exact ⟨hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2,hn2⟩
#print axioms OQ14.Packet06SchurModeLimit.convergent_kernel_modes
end OQ14.Packet06SchurModeLimit
