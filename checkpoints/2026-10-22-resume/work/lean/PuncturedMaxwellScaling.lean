import SourceDielectricMaxwell
import ModalScaling

/-! Actual source Maxwell fields at every positive frequency by spatial dilation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.PuncturedMaxwellScaling
open MeasureTheory Set Filter OQ14.Maxwell OQ14.ModalScaling OQ14.SourceRadialSystem
open scoped Topology

theorem dilated_test_avoids_origin (s : ℝ) (φ : Space → ℂ) (h0 : 0∉tsupport φ) :
    0∉tsupport (fun x : Space => φ (s • x)) := by
  rw [not_mem_tsupport_iff_eventuallyEq] at h0 ⊢
  exact h0.comp_tendsto (by simpa using (continuous_id.const_smul s).tendsto (0 : Space))

theorem weak_curl_dilate (s : ℝ) (hs : 0<s) (α : ℂ) (q : Space → ℂ) (E H : Field)
    (hw : ∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ → 0∉tsupport φ →
      weakCurlPairing E φ=fun j => ∫ x,(α*q x*H x j)*φ x)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (h0 : 0∉tsupport φ) :
    weakCurlPairing (dilate s E) φ=fun j => ∫ x,
      ((α/(s : ℂ))*q (s⁻¹ • x)*dilate s H x j)*φ x := by
  have he := hw (fun x => φ (s • x)) (dilated_test_contDiff s φ hφ)
    (dilated_test_compact s hs.ne' φ hc) (dilated_test_avoids_origin s φ h0)
  have hs0 : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [weakCurlPairing_dilate s hs E φ hφ,he]
  ext j
  simp only [Pi.smul_apply,smul_eq_mul]
  change (s : ℂ)^2*(∫ x,(α*q x*H x j)*φ (s • x))=_
  simp_rw [dilate]
  rw [integral_dilate_product s hs (fun y => (α/(s : ℂ))*q y*H y j) φ]
  simp_rw [mul_assoc,integral_const_mul]
  field_simp
  ring

def fieldAtFrequency (k : ℝ) (F : Field) : Field := fun x => F (k • x)
def coefficientAtFrequency (k : ℝ) (a : ℝ → ℂ) : Space → ℂ := fun x => a (k*‖x‖)

theorem weak_curl_at_frequency (k : ℝ) (hk : 0<k) (α : ℂ) (a : ℝ → ℂ) (E H : Field)
    (hw : ∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ → 0∉tsupport φ →
      weakCurlPairing E φ=fun j => ∫ x,(α*a ‖x‖*H x j)*φ x)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (h0 : 0∉tsupport φ) :
    weakCurlPairing (fieldAtFrequency k E) φ=fun j => ∫ x,
      (α*(k : ℂ)*coefficientAtFrequency k a x*fieldAtFrequency k H x j)*φ x := by
  have he : dilate k⁻¹ E=fieldAtFrequency k E := by
    ext x i
    simp only [dilate,fieldAtFrequency,inv_inv]
  rw [← he]
  simpa only [dilate,inv_inv,fieldAtFrequency,coefficientAtFrequency,Complex.ofReal_inv,
    div_eq_mul_inv,inv_inv,norm_smul,Real.norm_eq_abs,abs_of_pos hk] using
    weak_curl_dilate k⁻¹ (inv_pos.mpr hk) α (fun x => a ‖x‖) E H hw φ hφ hc h0

theorem tm_at_positive_frequency (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian p=0)
    (k : ℝ) (hk : 0<k) (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (fieldAtFrequency k (SourceUnclippedMaxwell.electric d p)) φ=(fun j => ∫ x,
      (Complex.I*(k : ℂ)*fieldAtFrequency k (SourceUnclippedMaxwell.magnetic d p) x j)*φ x) ∧
    weakCurlPairing (fieldAtFrequency k (SourceUnclippedMaxwell.magnetic d p)) φ=(fun j => ∫ x,
      (-Complex.I*(k : ℂ)*coefficientAtFrequency k (sigma d) x*
        fieldAtFrequency k (SourceUnclippedMaxwell.electric d p) x j)*φ x) := by
  constructor
  · simpa only [coefficientAtFrequency,mul_one] using
      weak_curl_at_frequency k hk Complex.I (fun _ => 1) _ _
        (fun ψ hψ hcψ h0ψ => by simpa only [mul_one] using
          (SourceDielectricMaxwell.tm_dielectric_weak d hdisp p hp hh ψ hψ hcψ h0ψ).1) φ hφ hc h0
  · exact weak_curl_at_frequency k hk (-Complex.I) (sigma d) _ _
      (fun ψ hψ hcψ h0ψ => (SourceDielectricMaxwell.tm_dielectric_weak d hdisp p hp hh ψ hψ hcψ h0ψ).2)
      φ hφ hc h0

theorem te_at_positive_frequency (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian p=0)
    (k : ℝ) (hk : 0<k) (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (fieldAtFrequency k (SourceGeneralMaxwell.teElectric d p)) φ=(fun j => ∫ x,
      (Complex.I*(k : ℂ)*fieldAtFrequency k (SourceGeneralMaxwell.teMagnetic d p) x j)*φ x) ∧
    weakCurlPairing (fieldAtFrequency k (SourceGeneralMaxwell.teMagnetic d p)) φ=(fun j => ∫ x,
      (-Complex.I*(k : ℂ)*coefficientAtFrequency k (SourceGeneralMaxwell.mu d) x*
        fieldAtFrequency k (SourceGeneralMaxwell.teElectric d p) x j)*φ x) := by
  constructor
  · simpa only [coefficientAtFrequency,mul_one] using
      weak_curl_at_frequency k hk Complex.I (fun _ => 1) _ _
        (fun ψ hψ hcψ h0ψ => by simpa only [mul_one] using
          (SourceDielectricMaxwell.te_dielectric_weak d hσ p hp hh ψ hψ hcψ h0ψ).1) φ hφ hc h0
  · exact weak_curl_at_frequency k hk (-Complex.I) (SourceGeneralMaxwell.mu d) _ _
      (fun ψ hψ hcψ h0ψ => (SourceDielectricMaxwell.te_dielectric_weak d hσ p hp hh ψ hψ hcψ h0ψ).2)
      φ hφ hc h0

end OQ14.PuncturedMaxwellScaling

#print axioms OQ14.PuncturedMaxwellScaling.dilated_test_avoids_origin
#print axioms OQ14.PuncturedMaxwellScaling.weak_curl_dilate
#print axioms OQ14.PuncturedMaxwellScaling.weak_curl_at_frequency
#print axioms OQ14.PuncturedMaxwellScaling.tm_at_positive_frequency
#print axioms OQ14.PuncturedMaxwellScaling.te_at_positive_frequency
