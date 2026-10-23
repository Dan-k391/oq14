import FiniteHerglotzCaps
import PlaneCapApproximation

/-! Actual smooth angular Maxwell cap fields approximate a fixed finite directional illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.FiniteCapApproximation
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel OQ14.ConicalRungeClosure
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere
abbrev μ := AngularPower.angularMeasure

theorem electric_integral (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (x : Space) (j : Fin 3) :
    FiniteHerglotzCaps.electric k c r hr x j=
      ∑ w ∈ c.support, c w*(∫ θ : Sphere, (SphereSmoothCaps.density w.1 r hr θ : ℂ)*
        ConicalPlaneWaves.electric k θ w.2 x j ∂μ) := by
  have hi (w : WaveIndex) : Integrable (fun θ : Sphere => c w*(SphereSmoothCaps.density w.1 r hr θ : ℂ)*
      ConicalPlaneWaves.polarization θ w.2 j*wave (-k) x θ) μ := by
    have hp : Continuous (fun θ : Sphere => ConicalPlaneWaves.polarization θ w.2 j) := by
      simp_rw [ConicalPlaneWaves.polarization_eq _ (AngularPower.sphere_norm _)]
      exact continuous_const.sub ((SphereWaveCalculus.coordinate_continuous w.2).mul (SphereWaveCalculus.coordinate_continuous j))
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp
      ((SphereSmoothCaps.ambient_smooth w.1 r hr).continuous.comp continuous_subtype_val))).mul hp |>.mul
        (by unfold wave; fun_prop)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [FiniteHerglotzCaps.electric,AngularHerglotz.electric,SphereWaveCalculus.moment,
    FiniteHerglotzCaps.amplitude_formula,Finset.sum_mul]
  change (∫ θ : Sphere, ∑ w ∈ c.support, c w*(SphereSmoothCaps.density w.1 r hr θ : ℂ)*
    ConicalPlaneWaves.polarization θ w.2 j*wave (-k) x θ ∂μ)=_
  rw [integral_finset_sum _ (fun w _ => hi w)]
  apply Finset.sum_congr rfl
  intro w _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  rw [PlaneCapApproximation.electric_as_wave]
  rw [ConicalPlaneWaves.polarization_eq (θ : Space) (AngularPower.sphere_norm θ) w.2 j,SphereReactionKernel.amplitude]
  ring

theorem uniform_electric_approximation (k R : ℝ) (c : WaveIndex →₀ ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ δ → ∀ x ∈ closedBall (0 : Space) R, ∀ j : Fin 3,
      ‖FiniteHerglotzCaps.electric k c r hr x j-ConicalFinitePlanes.electric k c x j‖ < ε := by
  let S : ℝ := ∑ w ∈ c.support, ‖c w‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hSp : 0 < S+1 := by linarith
  obtain ⟨δ,hδ,hbound⟩ := PlaneCapApproximation.uniform_cap_approximation k R (ε/(S+1)) (div_pos hε hSp)
  refine ⟨δ,hδ,?_⟩
  intro r hr hrδ x hx j
  rw [electric_integral,ConicalFinitePlanes.electric,Finsupp.sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ c.support, ‖c w*((∫ θ : Sphere, (SphereSmoothCaps.density w.1 r hr θ : ℂ)*
          ConicalPlaneWaves.electric k θ w.2 x j ∂μ)-ConicalPlaneWaves.electric k w.1 w.2 x j)‖ := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro w _
      rw [mul_sub]
    _ ≤ ∑ w ∈ c.support, ‖c w‖*(ε/(S+1)) := Finset.sum_le_sum (fun w _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound w.1 r hr hrδ x hx w.2 j) (norm_nonneg _))
    _ = S*(ε/(S+1)) := by rw [← Finset.sum_mul]
    _ < ε := by
      rw [← mul_div_assoc,div_lt_iff₀ hSp]
      nlinarith

end OQ14.FiniteCapApproximation
#print axioms OQ14.FiniteCapApproximation.electric_integral
#print axioms OQ14.FiniteCapApproximation.uniform_electric_approximation
