import Packet05FourierRepresentative
import VectorFourier
import Mathlib.MeasureTheory.Integral.Pi
import WeakPoynting

/-! Anisotropic Fourier weight for H1 fields with H1 tangential derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05AnisotropicEmbedding
open MeasureTheory Set OQ14.Maxwell
open scoped FourierTransform

def anisotropicWeight (x : Space) : ℝ :=
  (1 + (x 0)^2 + (x 1)^2) * (1 + (x 0)^2 + (x 1)^2 + (x 2)^2)

def coordinateMajorant (x : Space) : ℝ :=
  ∏ i : Fin 3, (1 + (x i)^2) ^ (-(2 : ℝ)/3)

theorem anisotropic_inverse_le_majorant (x : Space) :
    (anisotropicWeight x)⁻¹ ≤ coordinateMajorant x := by
  let a : ℝ := 1 + (x 0)^2 + (x 1)^2
  let b : ℝ := a + (x 2)^2
  let p : ℝ := (1+(x 0)^2)*(1+(x 1)^2)*(1+(x 2)^2)
  have ha : 1 ≤ a := by dsimp [a]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hab : a ≤ b := by dsimp [b]; nlinarith [sq_nonneg (x 2)]
  have hb : 1 ≤ b := ha.trans hab
  have hp : 0 < p := by dsimp [p]; positivity
  have hp01 : (1+(x 0)^2)*(1+(x 1)^2) ≤ a^2 := by
    have h0 : 1+(x 0)^2 ≤ a := by dsimp [a]; nlinarith [sq_nonneg (x 1)]
    have h1 : 1+(x 1)^2 ≤ a := by dsimp [a]; nlinarith [sq_nonneg (x 0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (show 0 ≤ 1+(x 1)^2 by positivity),
      mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ a by positivity)]
  have hp2 : 1+(x 2)^2 ≤ b := by dsimp [a,b]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hpbound : p ≤ a^2*b := by
    dsimp [p]
    have h := mul_le_mul hp01 hp2 (by positivity : 0 ≤ 1+(x 2)^2) (by positivity : 0 ≤ a^2)
    nlinarith
  have hp2bound : p^2 ≤ (a*b)^3 := by
    have hsq := pow_le_pow_left₀ hp.le hpbound 2
    have hmono : 0 ≤ (b-a) * (a^3*b^2) := mul_nonneg (sub_nonneg.mpr hab) (by positivity)
    nlinarith
  have hroot := Real.rpow_le_rpow (sq_nonneg p) hp2bound (by norm_num : 0 ≤ (1:ℝ)/3)
  have hroot' : p ^ ((2:ℝ)/3) ≤ a*b := by
    have hp2 : p^2 = p ^ (2:ℝ) := (Real.rpow_natCast p 2).symm
    have hab3 : (a*b)^3 = (a*b) ^ (3:ℝ) := (Real.rpow_natCast (a*b) 3).symm
    rw [hp2, hab3, ← Real.rpow_mul hp.le, ← Real.rpow_mul (by positivity : 0 ≤ a*b)] at hroot
    norm_num at hroot ⊢
    exact hroot
  have hpweight : 0 < p ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hp _
  have hinv : (a*b)⁻¹ ≤ (p ^ ((2:ℝ)/3))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpweight hroot'
  have hprod : coordinateMajorant x = (p ^ ((2:ℝ)/3))⁻¹ := by
    simp only [coordinateMajorant, Fin.prod_univ_three, p]
    rw [← Real.mul_rpow (by positivity : 0 ≤ 1+(x 0)^2) (by positivity : 0 ≤ 1+(x 1)^2),
      ← Real.mul_rpow (by positivity : 0 ≤ (1+(x 0)^2)*(1+(x 1)^2)) (by positivity : 0 ≤ 1+(x 2)^2)]
    rw [show (-(2:ℝ)/3) = -((2:ℝ)/3) by ring, Real.rpow_neg (by positivity)]
  simpa [anisotropicWeight, a, b, hprod] using hinv

/-- The explicit separable bound is integrable in all three coordinates. -/
theorem coordinateMajorant_integrable : Integrable coordinateMajorant := by
  have hg : Integrable (fun t : ℝ => (1+t^2) ^ (-(2 : ℝ)/3)) := by
    have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := (4:ℝ)/3)
      (by norm_num)
    convert hi using 1
    ext t
    simp only [Real.norm_eq_abs, sq_abs]
    congr 1
    norm_num
  have hp : Integrable (fun x : Fin 3 → ℝ =>
      ∏ i : Fin 3, (1+(x i)^2) ^ (-(2 : ℝ)/3)) :=
    Integrable.fintype_prod (fun _ : Fin 3 => hg)
  have hc := (VectorFourier.coordinateMap_preserving.integrable_comp_emb
    VectorFourier.coordinateMap.measurableEmbedding).2 hp
  simpa [coordinateMajorant, VectorFourier.coordinateMap, Function.comp_def] using hc

/-- The inverse anisotropic H1-in-normal/H1-in-tangential-derivative weight
is integrable in three dimensions. -/
theorem anisotropic_inverse_integrable : Integrable (fun x : Space => (anisotropicWeight x)⁻¹) := by
  apply coordinateMajorant_integrable.mono'
  · have hc : Continuous (fun x : Space => (anisotropicWeight x)⁻¹) := by
      apply Continuous.inv₀
      · unfold anisotropicWeight
        fun_prop
      · intro x
        unfold anisotropicWeight
        positivity
    exact hc.aestronglyMeasurable
  · filter_upwards with x
    have hnon : 0 ≤ (anisotropicWeight x)⁻¹ := by unfold anisotropicWeight; positivity
    change |(anisotropicWeight x)⁻¹| ≤ coordinateMajorant x
    rw [abs_of_nonneg hnon]
    exact anisotropic_inverse_le_majorant x

def spectralFactor (x : Space) : ℝ := Real.sqrt (anisotropicWeight x)

def spectralInverse (x : Space) : ℂ := ((spectralFactor x)⁻¹ : ℝ)

theorem spectralFactor_pos (x : Space) : 0 < spectralFactor x := by
  unfold spectralFactor anisotropicWeight
  positivity

theorem spectralInverse_memLp : MemLp spectralInverse 2 volume := by
  have hc : Continuous spectralInverse := by
    unfold spectralInverse spectralFactor
    apply Complex.continuous_ofReal.comp
    apply Continuous.inv₀
    · apply Continuous.sqrt
      unfold anisotropicWeight
      fun_prop
    · intro x
      exact ne_of_gt (spectralFactor_pos x)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  convert anisotropic_inverse_integrable using 1
  ext x
  have hn : 0 ≤ anisotropicWeight x := by unfold anisotropicWeight; positivity
  change ‖(((spectralFactor x)⁻¹ : ℝ) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (spectralFactor_pos x).le),
    inv_pow, show spectralFactor x ^ 2 = anisotropicWeight x from Real.sq_sqrt hn]

/-- The exact anisotropic spectral weight yields a continuous representative
and an explicit uniform bound. -/
theorem continuous_of_anisotropic_fourier (u : FourierL2.ScalarL2)
    (hweight : MemLp (fun x : Space => (spectralFactor x : ℂ) *
      (FourierL2.fourierEquiv.symm u) x) 2 volume) :
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ ‖spectralInverse_memLp.toLp spectralInverse‖ *
        ‖hweight.toLp (fun x : Space => (spectralFactor x : ℂ) *
          (FourierL2.fourierEquiv.symm u) x)‖ := by
  let v := FourierL2.fourierEquiv.symm u
  let p : Space → ℂ := fun x => (spectralFactor x : ℂ) * v x
  have hp : MemLp p 2 volume := hweight
  have hv : Integrable (v : Space → ℂ) := by
    have hi := spectralInverse_memLp.integrable_mul hp
    apply hi.congr
    filter_upwards with x
    change spectralInverse x * p x = v x
    have hn : (spectralFactor x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (spectralFactor_pos x).ne'
    simp only [spectralInverse, Complex.ofReal_inv, p]
    field_simp
  refine ⟨𝓕 (v : Space → ℂ), NewtonL1L2.ordinary_fourier_continuous hv, ?_, ?_⟩
  · have he := NewtonL1L2.fourierEquiv_ae_integral v hv
    simpa [v] using he
  · intro x
    have hb : (∫ ξ : Space, ‖v ξ‖) ≤
        ‖spectralInverse_memLp.toLp spectralInverse‖ * ‖hp.toLp p‖ := by
      calc
        _ = ∫ ξ : Space, ‖spectralInverse_memLp.toLp spectralInverse ξ‖ * ‖hp.toLp p ξ‖ := by
          apply integral_congr_ae
          filter_upwards [spectralInverse_memLp.coeFn_toLp, hp.coeFn_toLp] with ξ hq hp'
          rw [hq, hp']
          have hn : (spectralFactor ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (spectralFactor_pos ξ).ne'
          have he : spectralInverse ξ * p ξ = v ξ := by
            simp only [spectralInverse, Complex.ofReal_inv, p]
            field_simp
          rw [← norm_mul, he]
        _ ≤ _ := OQ14.WeakPoynting.integral_norm_mul_le _ _
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ Space) (v : Space → ℂ) x).trans hb

end OQ14.Packet05AnisotropicEmbedding
#print axioms OQ14.Packet05AnisotropicEmbedding.anisotropic_inverse_le_majorant
#print axioms OQ14.Packet05AnisotropicEmbedding.coordinateMajorant_integrable
#print axioms OQ14.Packet05AnisotropicEmbedding.anisotropic_inverse_integrable
#print axioms OQ14.Packet05AnisotropicEmbedding.spectralFactor_pos
#print axioms OQ14.Packet05AnisotropicEmbedding.spectralInverse_memLp
#print axioms OQ14.Packet05AnisotropicEmbedding.continuous_of_anisotropic_fourier
