import Packet05AnisotropicNormBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ExplicitAnisotropic
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05WeakFourier OQ14.Packet05AnisotropicEmbedding
  OQ14.Packet05AnisotropicWeakEmbedding OQ14.Packet05FourierDerivativeNorm
  OQ14.Packet05AnisotropicNormBound

abbrev Index := Unit ⊕ Fin 3 ⊕ (Fin 2 × Fin 3)

def term (v : Space → ℂ) : Index → Space → ℂ
  | .inl _, x => 2 * v x
  | .inr (.inl i), x => 2 * (x i : ℂ) * v x
  | .inr (.inr (i,j)), x => 2 * (x i.castSucc : ℂ) * (x j : ℂ) * v x

theorem spectral_majorant (v : Space → ℂ) (ξ : Space) :
    ‖(spectralFactor ξ : ℂ) * v ξ‖ ≤ ∑ i : Index, ‖term v i ξ‖ := by
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
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spectralFactor_pos ξ).le]
  have hq := mul_le_mul_of_nonneg_right hf (norm_nonneg (v ξ))
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two, Fintype.sum_unique, term, Fin.castSucc_zero, Fin.castSucc_one,
    norm_mul, Complex.norm_real, Real.norm_eq_abs] 
  norm_num
  nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1), abs_nonneg (ξ 2), norm_nonneg (v ξ),
    mul_nonneg (abs_nonneg (ξ 0)) (norm_nonneg (v ξ)),
    mul_nonneg (abs_nonneg (ξ 1)) (norm_nonneg (v ξ))]

end OQ14.Packet05ExplicitAnisotropic
#print axioms OQ14.Packet05ExplicitAnisotropic.spectral_majorant
