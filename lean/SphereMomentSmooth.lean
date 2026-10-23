import SphereWaveCalculus
import SphereParityDifferential
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Actual smoothness of sphere-integral waves with any continuous angular amplitude. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.SphereMomentSmooth
open MeasureTheory SphereReactionKernel SphereWaveCalculus Maxwell
open scoped Topology
abbrev Space := FourierL2.Space

theorem amplitude_bound_exists (a : Sphere → ℂ) (ha : Continuous a) : ∃ A : ℝ, ∀ θ, ‖a θ‖ ≤ A :=
  isCompact_univ.exists_bound_of_continuousOn ha.continuousOn |>.imp (fun _ h θ => h θ (Set.mem_univ _))

theorem moment_continuous (a : Sphere → ℂ) (ha : Continuous a) (k : ℝ) : Continuous (moment a k) := by
  obtain ⟨A,hA⟩ := amplitude_bound_exists a ha
  exact continuous_iff_continuousAt.mpr (fun x => (moment_hasFDerivAt a ha A hA k x).continuousAt)

theorem moment_fderiv_apply (a : Sphere → ℂ) (ha : Continuous a) (k : ℝ) (x v : Space) :
    fderiv ℝ (moment a k) x v=moment (fun θ => a θ*phase k θ v) k x := by
  obtain ⟨A,hA⟩ := amplitude_bound_exists a ha
  have hi : Integrable (fun θ : Sphere => (a θ*wave k x θ) • phase k θ) surface :=
    ((ha.mul (by unfold wave; fun_prop)).smul (phase_continuous k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [(moment_hasFDerivAt a ha A hA k x).fderiv,ContinuousLinearMap.integral_apply hi]
  unfold moment
  apply integral_congr_ae
  filter_upwards with θ
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem moment_contDiff_nat (n : ℕ) (a : Sphere → ℂ) (ha : Continuous a) (k : ℝ) :
    ContDiff ℝ (n : ℕ∞) (moment a k) := by
  induction n generalizing a with
  | zero => exact contDiff_zero.mpr (moment_continuous a ha k)
  | succ n ih =>
    have hn : (((n+1 : ℕ) : ℕ∞) : WithTop ℕ∞)=((n : ℕ∞) : WithTop ℕ∞)+1 := by norm_cast
    rw [hn,contDiff_succ_iff_fderiv_apply]
    obtain ⟨A,hA⟩ := amplitude_bound_exists a ha
    refine ⟨fun x => (moment_hasFDerivAt a ha A hA k x).differentiableAt,by simp,?_⟩
    intro v
    simp_rw [moment_fderiv_apply a ha k]
    exact ih _ (ha.mul ((ContinuousLinearMap.apply ℝ ℂ v).continuous.comp (phase_continuous k)))

theorem moment_smooth (a : Sphere → ℂ) (ha : Continuous a) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (moment a k) := contDiff_infty.mpr (fun n => moment_contDiff_nat n a ha k)

end OQ14.SphereMomentSmooth
#print axioms OQ14.SphereMomentSmooth.amplitude_bound_exists
#print axioms OQ14.SphereMomentSmooth.moment_continuous
#print axioms OQ14.SphereMomentSmooth.moment_fderiv_apply
#print axioms OQ14.SphereMomentSmooth.moment_contDiff_nat
#print axioms OQ14.SphereMomentSmooth.moment_smooth
