import ConicalAnnularTests
import ConicalInnerMaxwell

/-! Actual smooth-test Gauss law extends to the genuine conical angular H1 test for arbitrary L2 fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalLocalGauss
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalAnnularTests
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def epsilon (p : Data) : Space → ℝ := ConicalCapField.permittivity p.contrast p.threshold

theorem epsilon_bound (p : Data) (x : Space) : ‖epsilon p x‖ ≤ 1+p.contrast := by
  have h := ConicalStaticField.permittivity_bounds p.contrast p.threshold p.contrast_nonnegative x
  change ‖ConicalCapField.permittivity p.contrast p.threshold x‖ ≤ 1+p.contrast
  rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) h.1)]
  exact h.2

theorem displacement_memLp (p : Data) (E : Fin 3 → WeakCurl.L2Scalar) (i : Fin 3) :
    MemLp (fun x : Space => (epsilon p x : ℂ)*E i x) 2 volume := by
  apply (Lp.memLp (E i)).of_le_mul
  · exact (Complex.continuous_ofReal.measurable.comp
      (ConicalAnnularSource.permittivity_measurable p.contrast p.threshold)).aestronglyMeasurable.mul
      (Lp.memLp (E i)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (epsilon_bound p x) (norm_nonneg _)

def displacementL2 (p : Data) (E : Fin 3 → WeakCurl.L2Scalar) (i : Fin 3) : WeakCurl.L2Scalar :=
  (displacement_memLp p E i).toLp (fun x => (epsilon p x : ℂ)*E i x)

theorem displacementL2_ae (p : Data) (E : Fin 3 → WeakCurl.L2Scalar) (i : Fin 3) :
    (displacementL2 p E i : Space → ℂ) =ᵐ[volume] fun x => (epsilon p x : ℂ)*E i x :=
  (displacement_memLp p E i).coeFn_toLp

theorem angular_gauss (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn)
    (E : Fin 3 → WeakCurl.L2Scalar)
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
      (∑ i : Fin 3, ∫ x : Space, (epsilon p x : ℂ)*E i x*dcoord f x i)=0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∑ i : Fin 3, ∫ x : Space, (epsilon p x : ℂ)*E i x*angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  have hweak (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η) :
      (∑ i : Fin 3, ∫ x : Space, displacementL2 p E i x*dcoord f x i)=0 := by
    have he (i : Fin 3) : (∫ x : Space, displacementL2 p E i x*dcoord f x i)=
        ∫ x : Space, (epsilon p x : ℂ)*E i x*dcoord f x i :=
      integral_congr_ae ((displacementL2_ae p E i).mono (fun x hx => by dsimp only at hx ⊢; rw [hx]))
    simp only [he]
    apply hGauss f
    intro x hx
    simpa only [mem_ball,dist_zero_right] using (hs (hf hx)).2
  have hs' : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn :=
    fun r hr => ⟨(hs hr).1,(hs hr).2.trans hai⟩
  have h := divergence_angular_test p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos
    p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs' (displacementL2 p E) hweak
  have he (i : Fin 3) : (∫ x : Space, displacementL2 p E i x*angularDerivative p.eigenvalue p.threshold η x i)=
      ∫ x : Space, (epsilon p x : ℂ)*E i x*angularDerivative p.eigenvalue p.threshold η x i :=
    integral_congr_ae ((displacementL2_ae p E i).mono (fun x hx => by dsimp only at hx ⊢; rw [hx]))
  simpa only [he] using h

end OQ14.ConicalLocalGauss

#print axioms OQ14.ConicalLocalGauss.epsilon_bound
#print axioms OQ14.ConicalLocalGauss.displacement_memLp
#print axioms OQ14.ConicalLocalGauss.displacementL2_ae
#print axioms OQ14.ConicalLocalGauss.angular_gauss
