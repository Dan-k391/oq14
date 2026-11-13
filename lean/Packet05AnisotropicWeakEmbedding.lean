import Packet05WeakFourier

/-! The anisotropic Fourier weight follows from actual weak L² partials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05AnisotropicWeakEmbedding
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05WeakFourier OQ14.Packet05AnisotropicEmbedding

theorem anisotropic_weight_memLp_of_weak_partials (u : L2Scalar) (hu : CompactRepresentative u)
    (D : Fin 3 → L2Scalar) (hD : ∀ i, HasWeakPartial u (D i) i)
    (H : Fin 3 → Fin 3 → L2Scalar)
    (hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (D i) (H i j) j) :
    MemLp (fun ξ : Space => (spectralFactor ξ : ℂ) * FourierL2.fourierEquiv.symm u ξ) 2 volume := by
  let f := FourierL2.fourierEquiv.symm u
  let p : Fin 3 → Space → ℂ := fun i ξ => (ξ i : ℂ) * f ξ
  let m : Fin 3 → Fin 3 → Space → ℂ := fun i j ξ => (ξ i : ℂ) * (ξ j : ℂ) * f ξ
  have hp (i : Fin 3) : MemLp (p i) 2 volume := frequency_coordinate_memLp hu i (hD i)
  have hm0 (j : Fin 3) : MemLp (m 0 j) 2 volume :=
    frequency_mixed_memLp hu 0 j (hD 0) (hH 0 (by decide) j)
  have hm1 (j : Fin 3) : MemLp (m 1 j) 2 volume :=
    frequency_mixed_memLp hu 1 j (hD 1) (hH 1 (by decide) j)
  let major : Space → ℝ := fun ξ => 2 *
    (‖f ξ‖ + ‖p 0 ξ‖ + ‖p 1 ξ‖ + ‖p 2 ξ‖ +
      ‖m 0 0 ξ‖ + ‖m 0 1 ξ‖ + ‖m 0 2 ξ‖ +
      ‖m 1 0 ξ‖ + ‖m 1 1 ξ‖ + ‖m 1 2 ξ‖)
  have hmajor : MemLp major 2 volume := by
    exact (((((((((Lp.memLp f).norm.add (hp 0).norm).add (hp 1).norm).add (hp 2).norm).add
      (hm0 0).norm).add (hm0 1).norm).add (hm0 2).norm).add (hm1 0).norm).add
      (hm1 1).norm |>.add (hm1 2).norm).const_mul 2
  have hsf : Continuous spectralFactor := by
    unfold spectralFactor
    apply Continuous.sqrt
    unfold anisotropicWeight
    fun_prop
  apply hmajor.mono' ((Complex.continuous_ofReal.comp hsf).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards with ξ
  have ha : Real.sqrt (1+(ξ 0)^2+(ξ 1)^2) ≤ 1+|ξ 0|+|ξ 1| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), sq_abs (ξ 0), sq_abs (ξ 1),
        mul_nonneg (abs_nonneg (ξ 0)) (abs_nonneg (ξ 1))]
  have hb : Real.sqrt (1+(ξ 0)^2+(ξ 1)^2+(ξ 2)^2) ≤ 1+|ξ 0|+|ξ 1|+|ξ 2| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), abs_nonneg (ξ 2),
        sq_abs (ξ 0), sq_abs (ξ 1), sq_abs (ξ 2),
        mul_nonneg (abs_nonneg (ξ 0)) (abs_nonneg (ξ 1)),
        mul_nonneg (abs_nonneg (ξ 0)) (abs_nonneg (ξ 2)),
        mul_nonneg (abs_nonneg (ξ 1)) (abs_nonneg (ξ 2))]
  have hf : spectralFactor ξ ≤ (1+|ξ 0|+|ξ 1|)*(1+|ξ 0|+|ξ 1|+|ξ 2|) := by
    rw [spectralFactor, anisotropicWeight, Real.sqrt_mul (by positivity)]
    exact mul_le_mul ha hb (Real.sqrt_nonneg _) (by positivity)
  change ‖(spectralFactor ξ : ℂ) * f ξ‖ ≤ major ξ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spectralFactor_pos ξ).le]
  have hq := mul_le_mul_of_nonneg_right hf (norm_nonneg (f ξ))
  dsimp only [major, p, m]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), abs_nonneg (ξ 2), norm_nonneg (f ξ),
    mul_nonneg (abs_nonneg (ξ 0)) (norm_nonneg (f ξ)),
    mul_nonneg (abs_nonneg (ξ 1)) (norm_nonneg (f ξ))]

theorem continuous_of_weak_tangential_h1 (u : L2Scalar) (hu : CompactRepresentative u)
    (D : Fin 3 → L2Scalar) (hD : ∀ i, HasWeakPartial u (D i) i)
    (H : Fin 3 → Fin 3 → L2Scalar)
    (hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (D i) (H i j) j) :
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf, hu', _⟩ := continuous_of_anisotropic_fourier u
    (anisotropic_weight_memLp_of_weak_partials u hu D hD H hH)
  exact ⟨f, hf, hu'⟩

end OQ14.Packet05AnisotropicWeakEmbedding
#print axioms OQ14.Packet05AnisotropicWeakEmbedding.anisotropic_weight_memLp_of_weak_partials
#print axioms OQ14.Packet05AnisotropicWeakEmbedding.continuous_of_weak_tangential_h1
