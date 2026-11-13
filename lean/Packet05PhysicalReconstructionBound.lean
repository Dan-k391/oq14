import Packet05GraphTransmissionReconstruction

/-! Explicit physical-field bound from the transmission representatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05PhysicalReconstructionBound
open Maxwell Packet05GraphTransmissionReconstruction

theorem physical_field_norm (a b : ℝ) (ε t0 t1 n w0 w1 w2 : ℂ)
    (M E X : ℝ) (hM : 0 ≤ M) (hE : ‖ε⁻¹‖ ≤ E) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (ht0 : ‖t0‖ ≤ X) (ht1 : ‖t1‖ ≤ X) (hn : ‖n‖ ≤ X)
    (hw0 : ‖w0‖ ≤ X) (hw1 : ‖w1‖ ≤ X) (hw2 : ‖w2‖ ≤ X) (i : Fin 3) :
    ‖physicalField a b ε t0 t1 n w0 w1 w2 i‖ ≤ (2+(1+M)*(E+4*M+1))*X := by
  have hX : 0 ≤ X := (norm_nonneg t0).trans ht0
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hA : (1 : ℝ) ≤ 1+a^2+b^2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hinv : ‖(((1+a^2+b^2 : ℝ) : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1+a^2+b^2)]
    exact (inv_le_one₀ (by linarith : 0 < 1+a^2+b^2)).2 hA
  have hax : ‖(a : ℂ)‖ ≤ M := by simpa [Complex.norm_real,Real.norm_eq_abs] using ha
  have hbx : ‖(b : ℂ)‖ ≤ M := by simpa [Complex.norm_real,Real.norm_eq_abs] using hb
  have hnormal : ‖normalGradient a b ε t0 t1 n w0 w1 w2‖ ≤ (E+4*M+1)*X := by
    unfold normalGradient
    have h0 := norm_mul_le (ε⁻¹) n
    have h1 := norm_mul_le (a : ℂ) t0
    have h2 := norm_mul_le (b : ℂ) t1
    have h3 := norm_mul_le (a : ℂ) w0
    have h4 := norm_mul_le (b : ℂ) w1
    have hx0 := mul_le_mul hE hn (norm_nonneg _) hE0
    have hx1 := mul_le_mul hax ht0 (norm_nonneg _) hM
    have hx2 := mul_le_mul hbx ht1 (norm_nonneg _) hM
    have hx3 := mul_le_mul hax hw0 (norm_nonneg _) hM
    have hx4 := mul_le_mul hbx hw1 (norm_nonneg _) hM
    have hsum := norm_add_le (((ε⁻¹*n+(a : ℂ)*t0+(b : ℂ)*t1-w2)+(a : ℂ)*w0)) ((b : ℂ)*w1)
    have hsum1 := norm_add_le (ε⁻¹*n+(a : ℂ)*t0+(b : ℂ)*t1-w2) ((a : ℂ)*w0)
    have hsum2 := norm_sub_le (ε⁻¹*n+(a : ℂ)*t0+(b : ℂ)*t1) w2
    have hsum3 := norm_add_le (ε⁻¹*n+(a : ℂ)*t0) ((b : ℂ)*t1)
    have hsum4 := norm_add_le (ε⁻¹*n) ((a : ℂ)*t0)
    have hprod := norm_mul_le ((((1+a^2+b^2 : ℝ) : ℂ))⁻¹)
      (ε⁻¹*n+(a : ℂ)*t0+(b : ℂ)*t1-w2+(a : ℂ)*w0+(b : ℂ)*w1)
    have hi := mul_le_mul_of_nonneg_right hinv (norm_nonneg
      (ε⁻¹*n+(a : ℂ)*t0+(b : ℂ)*t1-w2+(a : ℂ)*w0+(b : ℂ)*w1))
    nlinarith
  have hn0 : 0 ≤ (E+4*M+1)*X := by positivity
  have hma := mul_le_mul hax hnormal (norm_nonneg _) hM
  have hmb := mul_le_mul hbx hnormal (norm_nonneg _) hM
  fin_cases i <;> simp [physicalField]
  · have h := (norm_add_le (t0-(a : ℂ)*normalGradient a b ε t0 t1 n w0 w1 w2) w0)
    have h' := norm_sub_le t0 ((a : ℂ)*normalGradient a b ε t0 t1 n w0 w1 w2)
    simp only [norm_mul] at h'
    nlinarith
  · have h := (norm_add_le (t1-(b : ℂ)*normalGradient a b ε t0 t1 n w0 w1 w2) w1)
    have h' := norm_sub_le t1 ((b : ℂ)*normalGradient a b ε t0 t1 n w0 w1 w2)
    simp only [norm_mul] at h'
    nlinarith
  · have h := norm_add_le (normalGradient a b ε t0 t1 n w0 w1 w2) w2
    nlinarith

end OQ14.Packet05PhysicalReconstructionBound
#print axioms OQ14.Packet05PhysicalReconstructionBound.physical_field_norm
