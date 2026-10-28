import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Algebra

noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false
open Complex MeasureTheory Metric Set Filter
open scoped Topology
namespace OQ14.CompactEntireLift
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

def lift (r : C(X, ℂ)) (f : ℂ → ℂ) (hf : Continuous f) (k : ℂ) : C(X, ℂ) :=
  ⟨fun x => f (k * r x), hf.comp (continuous_const.mul r.continuous)⟩

omit [CompactSpace X] [T2Space X] in
theorem continuous_lift (r : C(X, ℂ)) (f : ℂ → ℂ) (hf : Continuous f) :
    Continuous (lift r f hf) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.mul (r.continuous.comp continuous_snd))

theorem analyticAt_lift (r : C(X, ℂ)) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (k : ℂ) :
    AnalyticAt ℂ (lift r f hf.continuous) k := by
  let F := lift r f hf.continuous
  have hF : Continuous F := continuous_lift r f hf.continuous
  let G : ℂ → C(X, ℂ) := fun w => (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ z in C(k, (1 : ℝ)), (z - w)⁻¹ • F z
  have hG : AnalyticAt ℂ G k := by
    apply (hasFPowerSeriesOn_cauchy_integral (R := (1 : NNReal))
      (hF.continuousOn.circleIntegrable (by norm_num)) (by norm_num)).analyticAt
  apply hG.congr
  filter_upwards [isOpen_ball.mem_nhds (show k ∈ ball k (1 : ℝ) by simp)] with w hw
  apply ContinuousMap.ext
  intro x
  have hscalar : Differentiable ℂ (fun z => f (z * r x)) :=
    hf.comp (differentiable_id.mul_const (r x))
  have hformula := hscalar.differentiableOn.circleIntegral_sub_inv_smul hw
  have hi : CircleIntegrable (fun z => (z - w)⁻¹ • F z) k 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num)
    · apply ContinuousOn.smul _ hF.continuousOn
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz
      have : z ≠ w := by
        intro heq
        subst z
        have := hw
        rw [mem_ball] at this
        rw [mem_sphere] at hz
        linarith
      exact sub_ne_zero.mpr this

  have heval := (ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hi.out
  change (2 * Real.pi * I : ℂ)⁻¹ * (ContinuousMap.evalCLM ℂ x) (∮ z in C(k, (1 : ℝ)), (z - w)⁻¹ • F z) = f (w * r x) 
  rw [circleIntegral, ← heval]
  have hv : (∫ t : ℝ in (0)..2 * Real.pi, (ContinuousMap.evalCLM ℂ x) (deriv (circleMap k 1) t • (circleMap k 1 t - w)⁻¹ • F (circleMap k 1 t))) = (2 * Real.pi * I : ℂ) * f (w * r x) := by
    simpa only [map_smul, ContinuousMap.evalCLM_apply, F, lift, smul_eq_mul, circleIntegral] using hformula
  rw [hv, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

end OQ14.CompactEntireLift

#print axioms OQ14.CompactEntireLift.continuous_lift
#print axioms OQ14.CompactEntireLift.analyticAt_lift

