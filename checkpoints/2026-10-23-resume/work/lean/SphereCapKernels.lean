import SphereSmoothCaps
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Genuine cap averages approximate jointly continuous kernels uniformly on compact observation sets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.SphereCapKernels
open MeasureTheory Set Metric
open scoped Topology
abbrev Sphere := AngularPower.Sphere
abbrev μ := AngularPower.angularMeasure

theorem uniform_kernel_averaging {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Sphere × X → E) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Sphere) (r : ℝ) (hr : 0 < r), r ≤ δ → ∀ x : X,
      ‖(∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • f (θ,x) ∂μ)-f (n,x)‖ ≤ ε := by
  let F : C(Sphere,C(X,E)) := (⟨f,hf⟩ : C(Sphere × X,E)).curry
  obtain ⟨δ,hδ,hbound⟩ := SphereSmoothCaps.uniform_averaging F F.continuous ε hε
  refine ⟨δ,hδ,?_⟩
  intro n r hr hrδ x
  have hi : Integrable (fun θ : Sphere => SphereSmoothCaps.density n r hr θ • F θ) μ :=
    (((SphereSmoothCaps.ambient_smooth n r hr).continuous.comp continuous_subtype_val).smul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • F θ ∂μ) x=
      ∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • f (θ,x) ∂μ := by
    simpa only [ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,smul_eq_mul,
      F,ContinuousMap.curry_apply,ContinuousMap.coe_mk] using
      ((ContinuousMap.evalCLM ℝ x).integral_comp_comm hi).symm
  have hh := ContinuousMap.norm_coe_le_norm
    ((∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • F θ ∂μ)-F n) x
  have hle : ‖(∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • f (θ,x) ∂μ)-f (n,x)‖ ≤
      ‖(∫ θ : Sphere, SphereSmoothCaps.density n r hr θ • F θ ∂μ)-F n‖ := by
    simpa only [ContinuousMap.sub_apply,he,F,ContinuousMap.curry_apply,ContinuousMap.coe_mk] using hh
  exact hle.trans (hbound n r hr hrδ)

end OQ14.SphereCapKernels
#print axioms OQ14.SphereCapKernels.uniform_kernel_averaging
