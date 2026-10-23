import SphereMeasure
import AngularPower
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual smooth normalized angular caps obtained from Euclidean bump functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.SphereSmoothCaps
open MeasureTheory Set Metric
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Sphere := AngularPower.Sphere
abbrev μ := AngularPower.angularMeasure

def bump (n : Sphere) (r : ℝ) (hr : 0 < r) : ContDiffBump (n : Space) :=
  ⟨r/2,r,by linarith,by linarith⟩

def mass (n : Sphere) (r : ℝ) (hr : 0 < r) : ℝ := ∫ θ : Sphere, bump n r hr θ ∂μ

theorem bump_integrable (n : Sphere) (r : ℝ) (hr : 0 < r) :
    Integrable (fun θ : Sphere => bump n r hr θ) μ := by
  exact ((bump n r hr).continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem mass_pos (n : Sphere) (r : ℝ) (hr : 0 < r) : 0 < mass n r hr := by
  letI : Measure.IsOpenPosMeasure μ := SphereMeasure.volume_toSphere_openPos
  apply integral_pos_of_integrable_nonneg_nonzero
    ((bump n r hr).continuous.comp continuous_subtype_val) (bump_integrable n r hr)
    (fun θ => (bump n r hr).nonneg)
  have hn : bump n r hr (n : Space)=1 := (bump n r hr).one_of_mem_closedBall (by
    simp only [mem_closedBall,dist_self]; exact (bump n r hr).rIn_pos.le)
  exact hn.trans_ne one_ne_zero

def ambient (n : Sphere) (r : ℝ) (hr : 0 < r) : Space → ℝ := fun y => bump n r hr y/mass n r hr

def density (n : Sphere) (r : ℝ) (hr : 0 < r) : Sphere → ℝ := fun θ => ambient n r hr θ

theorem ambient_smooth (n : Sphere) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (ambient n r hr) := (bump n r hr).contDiff.div_const _

theorem density_nonneg (n : Sphere) (r : ℝ) (hr : 0 < r) (θ : Sphere) : 0 ≤ density n r hr θ :=
  div_nonneg (bump n r hr).nonneg (mass_pos n r hr).le

theorem density_integrable (n : Sphere) (r : ℝ) (hr : 0 < r) : Integrable (density n r hr) μ :=
  (bump_integrable n r hr).div_const _

theorem density_mass (n : Sphere) (r : ℝ) (hr : 0 < r) : (∫ θ : Sphere, density n r hr θ ∂μ)=1 := by
  simp only [density,ambient,integral_div,mass]
  exact div_self (mass_pos n r hr).ne'

theorem density_zero (n : Sphere) (r : ℝ) (hr : 0 < r) (θ : Sphere)
    (hθ : r ≤ dist θ n) : density n r hr θ=0 := by
  have h : bump n r hr (θ : Space)=0 := (bump n r hr).zero_of_le_dist hθ
  simp only [density,ambient,h,zero_div]

theorem averaging_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Sphere → E) (hf : Continuous f) (n : Sphere) (r ε : ℝ) (hr : 0 < r) (_hε : 0 ≤ ε)
    (hlocal : ∀ θ : Sphere, dist θ n < r → ‖f θ-f n‖ ≤ ε) :
    ‖(∫ θ : Sphere, density n r hr θ • f θ ∂μ)-f n‖ ≤ ε := by
  have hd := density_integrable n r hr
  have hc : Continuous (density n r hr) := (ambient_smooth n r hr).continuous.comp continuous_subtype_val
  have hi : Integrable (fun θ : Sphere => density n r hr θ • (f θ-f n)) μ :=
    (hc.smul (hf.sub continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hif : Integrable (fun θ : Sphere => density n r hr θ • f θ) μ :=
    (hc.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ θ : Sphere, density n r hr θ • f θ ∂μ)-f n=
      ∫ θ : Sphere, density n r hr θ • (f θ-f n) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hif (hd.smul_const _),integral_smul_const,density_mass,one_smul]
  rw [he]
  have hb : ‖∫ θ : Sphere, density n r hr θ • (f θ-f n) ∂μ‖ ≤
      ∫ θ : Sphere, density n r hr θ*ε ∂μ := by
    apply norm_integral_le_of_norm_le (hd.mul_const ε)
    filter_upwards with θ
    by_cases hθ : dist θ n < r
    · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (density_nonneg n r hr θ)]
      exact mul_le_mul_of_nonneg_left (hlocal θ hθ) (density_nonneg n r hr θ)
    · rw [density_zero n r hr θ (not_lt.mp hθ),zero_smul,norm_zero,zero_mul]
  exact hb.trans_eq (by rw [integral_mul_const,density_mass,one_mul])

theorem uniform_averaging {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Sphere → E) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Sphere) (r : ℝ) (hr : 0 < r), r ≤ δ →
      ‖(∫ θ : Sphere, density n r hr θ • f θ ∂μ)-f n‖ ≤ ε := by
  obtain ⟨δ,hδ,hbound⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  refine ⟨δ,hδ,?_⟩
  intro n r hr hrδ
  apply averaging_error f hf n r ε hr hε.le
  intro θ hθ
  simpa only [dist_eq_norm] using (hbound (hθ.trans_le hrδ)).le

end OQ14.SphereSmoothCaps
#print axioms OQ14.SphereSmoothCaps.bump_integrable
#print axioms OQ14.SphereSmoothCaps.mass_pos
#print axioms OQ14.SphereSmoothCaps.ambient_smooth
#print axioms OQ14.SphereSmoothCaps.density_nonneg
#print axioms OQ14.SphereSmoothCaps.density_integrable
#print axioms OQ14.SphereSmoothCaps.density_mass
#print axioms OQ14.SphereSmoothCaps.density_zero
#print axioms OQ14.SphereSmoothCaps.averaging_error
#print axioms OQ14.SphereSmoothCaps.uniform_averaging
