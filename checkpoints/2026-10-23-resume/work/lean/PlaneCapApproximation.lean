import SphereCapKernels
import ConicalFinitePlanes

/-! Actual angular cap averages of transverse directional plane waves converge uniformly on spatial balls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.PlaneCapApproximation
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel
open scoped Topology InnerProductSpace
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere
abbrev μ := AngularPower.angularMeasure

theorem electric_as_wave (k : ℝ) (θ : Sphere) (i j : Fin 3) (x : Space) :
    ConicalPlaneWaves.electric k θ i x j=amplitude θ i j*wave (-k) x θ := by
  simp only [ConicalPlaneWaves.electric,exponentialField,exponential,ConicalPlaneWaves.linearPhase_eq,
    ConicalPlaneWaves.polarization_eq _ (AngularPower.sphere_norm θ),amplitude,wave]
  congr 1
  push_cast
  ring_nf

theorem electric_joint_continuous (k : ℝ) (i j : Fin 3) :
    Continuous (fun q : Sphere × Space => ConicalPlaneWaves.electric k q.1 i q.2 j) := by
  simp_rw [electric_as_wave]
  exact (SphereReactionKernel.integrand_continuous (-k) i j).comp (continuous_snd.prodMk continuous_fst)

def matrixKernel (k R : ℝ) (q : Sphere × closedBall (0 : Space) R) : Fin 3 → Fin 3 → ℂ :=
  fun i j => ConicalPlaneWaves.electric k q.1 i q.2 j

theorem matrixKernel_continuous (k R : ℝ) : Continuous (matrixKernel k R) :=
  continuous_pi (fun i => continuous_pi (fun j => (electric_joint_continuous k i j).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))))

theorem uniform_cap_approximation (k R ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Sphere) (r : ℝ) (hr : 0 < r), r ≤ δ →
      ∀ (x : Space), x ∈ closedBall (0 : Space) R → ∀ i j : Fin 3,
      ‖(∫ θ : Sphere, (SphereSmoothCaps.density n r hr θ : ℂ)*ConicalPlaneWaves.electric k θ i x j ∂μ)-
        ConicalPlaneWaves.electric k n i x j‖ ≤ ε := by
  letI : CompactSpace (closedBall (0 : Space) R) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space) R)
  obtain ⟨δ,hδ,hb⟩ := SphereCapKernels.uniform_kernel_averaging (matrixKernel k R) (matrixKernel_continuous k R) ε hε
  refine ⟨δ,hδ,?_⟩
  intro n r hr hrδ x hx i j
  let F := fun θ : Sphere => SphereSmoothCaps.density n r hr θ • matrixKernel k R (θ,⟨x,hx⟩)
  have hi : Integrable F μ :=
    (((SphereSmoothCaps.ambient_smooth n r hr).continuous.comp continuous_subtype_val).smul
      ((matrixKernel_continuous k R).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let L : (Fin 3 → Fin 3 → ℂ) →L[ℝ] ℂ := (ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : (Fin 3 → Fin 3 → ℂ) →L[ℝ] (Fin 3 → ℂ))
  have he : (∫ θ : Sphere, F θ ∂μ) i j=
      ∫ θ : Sphere, (SphereSmoothCaps.density n r hr θ : ℂ)*ConicalPlaneWaves.electric k θ i x j ∂μ := by
    simpa only [L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,F,Pi.smul_apply,smul_eq_mul,matrixKernel] using
      (L.integral_comp_comm hi).symm
  have hn := (norm_le_pi_norm
    (((∫ θ : Sphere, F θ ∂μ)-matrixKernel k R (n,⟨x,hx⟩)) i) j).trans
      (norm_le_pi_norm ((∫ θ : Sphere, F θ ∂μ)-matrixKernel k R (n,⟨x,hx⟩)) i)
  have hs : ‖(∫ θ : Sphere, (SphereSmoothCaps.density n r hr θ : ℂ)*ConicalPlaneWaves.electric k θ i x j ∂μ)-
      ConicalPlaneWaves.electric k n i x j‖ ≤ ‖(∫ θ : Sphere, F θ ∂μ)-matrixKernel k R (n,⟨x,hx⟩)‖ := by
    simpa only [Pi.sub_apply,he,matrixKernel] using hn
  exact hs.trans (hb n r hr hrδ ⟨x,hx⟩)

end OQ14.PlaneCapApproximation
#print axioms OQ14.PlaneCapApproximation.electric_as_wave
#print axioms OQ14.PlaneCapApproximation.electric_joint_continuous
#print axioms OQ14.PlaneCapApproximation.matrixKernel_continuous
#print axioms OQ14.PlaneCapApproximation.uniform_cap_approximation
