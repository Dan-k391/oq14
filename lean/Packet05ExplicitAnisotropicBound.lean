import Packet05ExplicitAnisotropic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ExplicitAnisotropicBound
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05WeakFourier OQ14.Packet05AnisotropicEmbedding
  OQ14.Packet05AnisotropicWeakEmbedding OQ14.Packet05FourierDerivativeNorm
  OQ14.Packet05AnisotropicNormBound OQ14.Packet05ExplicitAnisotropic

variable (u : L2Scalar) (hu : CompactRepresentative u)
    (D : Fin 3 → L2Scalar) (hD : ∀ i, HasWeakPartial u (D i) i)
    (H : Fin 3 → Fin 3 → L2Scalar)
    (hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (D i) (H i j) j)

def term_mem : ∀ i : Index, MemLp (term (FourierL2.fourierEquiv.symm u) i) 2 volume
  | .inl _ => by
      change MemLp (fun x => 2 * FourierL2.fourierEquiv.symm u x) 2 volume
      simpa using (Lp.memLp (FourierL2.fourierEquiv.symm u)).const_mul 2
  | .inr (.inl i) => by
      change MemLp (fun x => 2 * (x i : ℂ) * FourierL2.fourierEquiv.symm u x) 2 volume
      simpa [mul_assoc] using (frequency_coordinate_memLp hu i (hD i)).const_mul 2
  | .inr (.inr (i,j)) => by
      have hi : i.castSucc ≠ (2 : Fin 3) := by fin_cases i <;> decide
      change MemLp (fun x => 2 * (x i.castSucc : ℂ) * (x j : ℂ) * FourierL2.fourierEquiv.symm u x) 2 volume
      simpa [mul_assoc] using (frequency_mixed_memLp hu i.castSucc j (hD i.castSucc) (hH i.castSucc hi j)).const_mul 2

theorem term_norm (i : Index) :
    ‖(term_mem u hu D hD H hH i).toLp (term (FourierL2.fourierEquiv.symm u) i)‖ =
    match i with
    | .inl _ => 2 * ‖u‖
    | .inr (.inl k) => 2 * (‖fourierConstant⁻¹‖ * ‖D k‖)
    | .inr (.inr (k,j)) => 2 * (‖fourierConstant⁻¹‖^2 * ‖H k.castSucc j‖) := by
  cases i with
  | inl a =>
    cases a
    have hh := congrArg norm (MemLp.toLp_const_smul (2 : ℂ) (Lp.memLp (FourierL2.fourierEquiv.symm u)))
    rw [norm_smul, Lp.toLp_coeFn, FourierL2.fourierEquiv.symm.norm_map] at hh
    simpa [term, Pi.smul_apply, smul_eq_mul, Lp.norm_toLp] using hh
  | inr b =>
    cases b with
    | inl k =>
      have hh := congrArg norm (MemLp.toLp_const_smul (2 : ℂ) (frequency_coordinate_memLp hu k (hD k)))
      rw [norm_smul, coordinate_factor_norm u (D k) hu k (hD k)] at hh
      change ‖(term_mem u hu D hD H hH (.inr (.inl k))).toLp (fun x => 2 * (x k : ℂ) * FourierL2.fourierEquiv.symm u x)‖ = 2 * (‖fourierConstant⁻¹‖ * ‖D k‖)
      simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, Lp.norm_toLp] using hh
    | inr q =>
      obtain ⟨k,j⟩ := q
      have hk : k.castSucc ≠ (2 : Fin 3) := by fin_cases k <;> decide
      have hh := congrArg norm (MemLp.toLp_const_smul (2 : ℂ) (frequency_mixed_memLp hu k.castSucc j (hD k.castSucc) (hH k.castSucc hk j)))
      rw [norm_smul, mixed_factor_norm u (D k.castSucc) (H k.castSucc j) hu k.castSucc j (hD k.castSucc) (hH k.castSucc hk j)] at hh
      change ‖(term_mem u hu D hD H hH (.inr (.inr (k,j)))).toLp (fun x => 2 * (x k.castSucc : ℂ) * (x j : ℂ) * FourierL2.fourierEquiv.symm u x)‖ = 2 * (‖fourierConstant⁻¹‖^2 * ‖H k.castSucc j‖)
      simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, Lp.norm_toLp] using hh


def universalConstant : ℝ :=
  2 * ‖spectralInverse_memLp.toLp spectralInverse‖ *
    (1 + ‖fourierConstant⁻¹‖ + ‖fourierConstant⁻¹‖^2)

include hu hD hH in
theorem continuous_sup_bound :
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ universalConstant *
        (‖u‖ + ∑ i : Fin 3, ‖D i‖ + ∑ i : Fin 2, ∑ j : Fin 3, ‖H i.castSucc j‖) := by
  let hw := anisotropic_weight_memLp_of_weak_partials u hu D hD H hH
  have hf := finite_majorant
    (fun x : Space => (spectralFactor x : ℂ) * FourierL2.fourierEquiv.symm u x) hw
    (term (FourierL2.fourierEquiv.symm u)) (term_mem u hu D hD H hH)
    (spectral_majorant (FourierL2.fourierEquiv.symm u))
  simp only [term_norm u hu D hD H hH, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, Fintype.sum_unique,
    Fin.castSucc_zero, Fin.castSucc_one] at hf
  obtain ⟨f,hcont,hae,hbound⟩ :=
    OQ14.Packet05QuantitativeAnisotropic.continuous_weak_tangential_h1_bound u hu D hD H hH
  refine ⟨f,hcont,hae,?_⟩
  intro x
  have hm : ‖hw.toLp (fun x : Space => (spectralFactor x : ℂ) * FourierL2.fourierEquiv.symm u x)‖ ≤
      2 * (1 + ‖fourierConstant⁻¹‖ + ‖fourierConstant⁻¹‖^2) *
        (‖u‖ + ∑ i : Fin 3, ‖D i‖ + ∑ i : Fin 2, ∑ j : Fin 3, ‖H i.castSucc j‖) := by
    simp only [Fin.sum_univ_three, Fin.sum_univ_two, Fin.castSucc_zero, Fin.castSucc_one]
    nlinarith [norm_nonneg u, norm_nonneg (D 0), norm_nonneg (D 1), norm_nonneg (D 2),
      norm_nonneg (H 0 0), norm_nonneg (H 0 1), norm_nonneg (H 0 2),
      norm_nonneg (H 1 0), norm_nonneg (H 1 1), norm_nonneg (H 1 2),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg u),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg u),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (u)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (D 0)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (D 1)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (D 2)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 0 0)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 0 1)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 0 2)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 1 0)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 1 1)),
      mul_nonneg (norm_nonneg (fourierConstant⁻¹)) (norm_nonneg (H 1 2)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (u)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (D 0)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (D 1)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (D 2)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 0 0)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 0 1)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 0 2)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 1 0)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 1 1)),
      mul_nonneg (sq_nonneg ‖fourierConstant⁻¹‖) (norm_nonneg (H 1 2))]
  exact (hbound x).trans (by
    have h := mul_le_mul_of_nonneg_left hm (norm_nonneg (spectralInverse_memLp.toLp spectralInverse))
    simpa only [universalConstant] using (show
      ‖spectralInverse_memLp.toLp spectralInverse‖ * _ ≤
        universalConstant * (‖u‖ + ∑ i : Fin 3, ‖D i‖ + ∑ i : Fin 2, ∑ j : Fin 3, ‖H i.castSucc j‖) by
          dsimp only [universalConstant]; nlinarith))

end OQ14.Packet05ExplicitAnisotropicBound
#print axioms OQ14.Packet05ExplicitAnisotropicBound.term_norm

#print axioms OQ14.Packet05ExplicitAnisotropicBound.continuous_sup_bound
