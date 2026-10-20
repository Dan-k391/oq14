import ModalPoleRadiation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Actual positive spatial dilation of the residue Maxwell mode

The coordinate change retains the weak equations and the exponential
radiation weight. Frequencies are divided by the physical sphere radius.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalScaling

open Complex MeasureTheory Filter OQ14.Maxwell OQ14.ModalProfiles OQ14.ModalAlgebra
  OQ14.ModalMatching OQ14.ModalFieldResidue OQ14.ModalPoleMode
  OQ14.ModalOutgoing OQ14.ModalPoleRadiation OQ14.ModalShell OQ14.ModalFieldPole
open scoped Topology

def dilate (s : ℝ) (F : Field) : Field := fun x => F (s⁻¹ • x)

def sphereCoefficient (n : ℂ) (s : ℝ) (x : Space) : ℂ :=
  if ‖x‖ ≤ s then n^2 else 1

theorem dcoord_comp_smul (a : ℝ) (φ : Space → ℂ) (x : Space)
    (hφ : DifferentiableAt ℝ φ (a • x)) (j : Fin 3) :
    dcoord (fun y => φ (a • y)) x j = (a : ℂ) * dcoord φ (a • x) j := by
  have h := hφ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  change (fderiv ℝ (φ ∘ HSMul.hSMul a) x) (basis j) = _
  rw [h.fderiv]
  simp [dcoord, ContinuousLinearMap.comp_apply, Complex.real_smul]

theorem curl_dilate (s : ℝ) (F : Field) (x : Space)
    (hF : ∀ j, DifferentiableAt ℝ (fun y => F y j) (s⁻¹ • x)) :
    curl (dilate s F) x = ((s : ℂ)⁻¹) • curl F (s⁻¹ • x) := by
  ext j
  fin_cases j <;> simp only [curl, pd, dilate, dcoord_comp_smul s⁻¹ _ x (hF _),
    Complex.ofReal_inv, Pi.smul_apply, smul_eq_mul] <;> dsimp <;> ring

theorem dilated_test_contDiff (s : ℝ) (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun x => φ (s • x)) :=
  hφ.comp (contDiff_id.const_smul s)

theorem dilated_test_compact (s : ℝ) (hs : s ≠ 0) (φ : Space → ℂ)
    (hc : HasCompactSupport φ) : HasCompactSupport (fun x => φ (s • x)) := by
  exact hc.comp_homeomorph (Homeomorph.smul (Units.mk0 s hs))

theorem integral_dilate_product (s : ℝ) (hs : 0 < s) (q φ : Space → ℂ) :
    (∫ x, q (s⁻¹ • x) * φ x) = (s : ℂ)^3 * ∫ y, q y * φ (s • y) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Space)
    (fun y => q y * φ (s • y)) hs.le
  simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul,
    finrank_euclideanSpace, Fintype.card_fin, Complex.real_smul, Complex.ofReal_pow] using h

theorem integral_dilate_derivative (s : ℝ) (hs : 0 < s) (q φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (j : Fin 3) :
    (∫ x, q (s⁻¹ • x) * dcoord φ x j) =
      (s : ℂ)^2 * ∫ y, q y * dcoord (fun z => φ (s • z)) y j := by
  rw [integral_dilate_product s hs]
  simp_rw [dcoord_comp_smul s φ _ (hφ.differentiable (by norm_num)).differentiableAt j]
  simp_rw [mul_left_comm (q _) (s : ℂ)]
  rw [integral_const_mul]
  ring

theorem weakCurlPairing_dilate (s : ℝ) (hs : 0 < s) (F : Field)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) :
    weakCurlPairing (dilate s F) φ =
      (s : ℂ)^2 • weakCurlPairing F (fun x => φ (s • x)) := by
  have hI (i j : Fin 3) := integral_dilate_derivative s hs (fun x => F x i) φ hφ j
  ext j
  fin_cases j <;> simp only [weakCurlPairing, dilate,
    Pi.smul_apply, smul_eq_mul] <;> dsimp <;> rw [hI, hI] <;> ring

theorem sphereCoefficient_dilate (n : ℂ) (s : ℝ) (hs : 0 < s) (x : Space) :
    sphereCoefficient n s x = coefficient n (s⁻¹ • x) := by
  have hn : ‖s⁻¹ • x‖ = ‖x‖ / s := by
    simp [norm_smul, abs_of_pos hs, div_eq_mul_inv, mul_comm]
  simp only [sphereCoefficient, coefficient, hn, div_le_one hs]

theorem weak_maxwell_dilate (s : ℝ) (hs : 0 < s) (n k : ℂ) (E H : Field)
    (hw : ∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      weakCurlPairing E φ = (fun j => ∫ x, (I*k*H x j)*φ x) ∧
      weakCurlPairing H φ = (fun j => ∫ x, (-I*k*coefficient n x*E x j)*φ x))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (dilate s E) φ =
        (fun j => ∫ x, (I*(k/(s : ℂ))*dilate s H x j)*φ x) ∧
      weakCurlPairing (dilate s H) φ =
        (fun j => ∫ x, (-I*(k/(s : ℂ))*sphereCoefficient n s x*dilate s E x j)*φ x) := by
  obtain ⟨he,hh⟩ := hw (fun x => φ (s • x)) (dilated_test_contDiff s φ hφ)
    (dilated_test_compact s hs.ne' φ hc)
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  constructor
  · rw [weakCurlPairing_dilate s hs E φ hφ, he]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    change (s : ℂ)^2 * (∫ x, (I*k*H x j)*φ (s • x)) = _
    simp_rw [dilate]
    rw [integral_dilate_product s hs (fun y => I*(k/(s : ℂ))*H y j) φ]
    simp_rw [mul_assoc, integral_const_mul]
    field_simp
    ring
  · rw [weakCurlPairing_dilate s hs H φ hφ, hh]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    change (s : ℂ)^2 * (∫ x, (-I*k*coefficient n x*E x j)*φ (s • x)) = _
    simp_rw [dilate, sphereCoefficient_dilate n s hs]
    rw [integral_dilate_product s hs
      (fun y => -I*(k/(s : ℂ))*coefficient n y*E y j) φ]
    simp_rw [mul_assoc, integral_const_mul]
    field_simp
    ring

theorem residue_weak_maxwell_dilate (s : ℝ) (hs : 0 < s) (n k : ℂ)
    (hn : n ≠ 0) (hk : k ≠ 0) (hd : tmDet 1 n k = 0) (f : Amplitudes)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (dilate s (electricMode n k f)) φ =
        (fun j => ∫ x, (I*(k/(s : ℂ))*dilate s (magneticMode n k f) x j)*φ x) ∧
      weakCurlPairing (dilate s (magneticMode n k f)) φ =
        (fun j => ∫ x, (-I*(k/(s : ℂ))*sphereCoefficient n s x*
          dilate s (electricMode n k f) x j)*φ x) :=
  weak_maxwell_dilate s hs n k _ _ (residue_weak_maxwell n k hn hk hd f) φ hφ hc

theorem tangent_real_smul (a : ℝ) (x : Space) (v : Vector) :
    OQ14.ModalInterface.tangent (a • x) v =
      (a : ℂ) • OQ14.ModalInterface.tangent x v := by
  ext j
  fin_cases j <;> simp [OQ14.ModalInterface.tangent, cross_apply,
    PiLp.smul_apply, Complex.ofReal_mul] <;> ring

theorem normalized_tangent_dilate (s : ℝ) (hs : 0 < s) (x : Space) (v : Vector) :
    ((‖s⁻¹ • x‖ : ℂ)⁻¹) • OQ14.ModalInterface.tangent (s⁻¹ • x) v =
      ((‖x‖ : ℂ)⁻¹) • OQ14.ModalInterface.tangent x v := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  rw [tangent_real_smul, smul_smul]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev, inv_inv]
  by_cases hx : (‖x‖ : ℂ) = 0
  · simp [hx]
  · field_simp [hs0, hx]
    ring

def dilatedRadiationDefect (s : ℝ) (n k : ℂ) (f : Amplitudes) (x : Space) : Vector :=
  (Complex.exp (-I*(k/(s : ℂ))*‖x‖)*(‖x‖ : ℂ)) •
    (dilate s (magneticMode n k f) x -
      ((‖x‖ : ℂ)⁻¹) • OQ14.ModalInterface.tangent x (dilate s (electricMode n k f) x))

theorem dilatedRadiationDefect_eq (s : ℝ) (hs : 0 < s) (n k : ℂ)
    (f : Amplitudes) (x : Space) :
    dilatedRadiationDefect s n k f x =
      (s : ℂ) • modeRadiationDefect n k f (s⁻¹ • x) := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hn : (‖s⁻¹ • x‖ : ℂ) = (s : ℂ)⁻¹ * (‖x‖ : ℂ) := by
    simp [norm_smul, abs_of_pos hs, Complex.ofReal_mul]
  unfold dilatedRadiationDefect modeRadiationDefect dilate
  rw [normalized_tangent_dilate s hs, smul_smul, hn]
  congr 1
  have he : -I*(k/(s : ℂ))*(‖x‖ : ℂ) = -I*k*((s : ℂ)⁻¹*(‖x‖ : ℂ)) := by ring
  rw [he]
  field_simp

theorem dilatedRadiationDefect_limit (s : ℝ) (hs : 0 < s) (n k : ℂ)
    (hk : k ≠ 0) (f : Amplitudes)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => dilatedRadiationDefect s n k f (γ t)) atTop (𝓝 0) := by
  have hrad : Tendsto (fun t => ‖s⁻¹ • γ t‖) atTop atTop := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs] using
      hγ.const_mul_atTop (inv_pos.mpr hs)
  have ht := (tendsto_const_nhds (x := (s : ℂ))).smul
    (modeRadiationDefect_limit n k hk f (fun t => s⁻¹ • γ t) hrad)
  simpa only [smul_zero, ← dilatedRadiationDefect_eq s hs] using ht

theorem frequency_dilate (k : ℂ) (s : ℝ) (hs : 0 < s) :
    (k/(s : ℂ)).re = k.re/s ∧ (k/(s : ℂ)).im = k.im/s ∧
      (k/(s : ℂ)).re / (-2*(k/(s : ℂ)).im) = k.re / (-2*k.im) := by
  have hr : (k/(s : ℂ)).re = k.re/s := Complex.div_ofReal_re k s
  have hi : (k/(s : ℂ)).im = k.im/s := Complex.div_ofReal_im k s
  refine ⟨hr, hi, ?_⟩
  rw [hr, hi]
  field_simp

theorem prescribed_frequency_scale (k : ℂ) (hk : 0 < k.re) (hki : k.im < 0)
    (k0 : ℝ) (hk0 : 0 < k0) :
    let s := k.re/k0
    0 < s ∧ (k/(s : ℂ)).re = k0 ∧ (k/(s : ℂ)).im < 0 ∧
      (k/(s : ℂ)).re / (-2*(k/(s : ℂ)).im) = k.re / (-2*k.im) := by
  dsimp only
  have hs : 0 < k.re/k0 := div_pos hk hk0
  obtain ⟨hr,hi,hq⟩ := frequency_dilate k (k.re/k0) hs
  refine ⟨hs, ?_, ?_, hq⟩
  · rw [hr]
    field_simp
  · rw [hi]
    exact div_neg_of_neg_of_pos hki hs

theorem scaled_ray_identity (s : ℝ) (hs : 0 < s) (k : ℂ)
    (F : Field) (r : ℝ) (d : Space) :
    (Complex.exp (-I*(k/(s : ℂ))*r)*(r : ℂ)) • dilate s F (r • d) =
      (s : ℂ) • ((Complex.exp (-I*k*(r/s : ℝ))*(r/s : ℝ)) • F ((r/s) • d)) := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have ha : s⁻¹*r = r/s := by rw [div_eq_mul_inv, mul_comm]
  simp only [dilate, smul_smul, ha]
  congr 1
  have he : -I*(k/(s : ℂ))*(r : ℂ) = -I*k*(r/s : ℝ) := by
    push_cast
    ring
  rw [he]
  push_cast
  field_simp

theorem dilate_ray_far_limit (s : ℝ) (hs : 0 < s) (k : ℂ)
    (F : Field) (d : Space) (A : Vector)
    (hF : Tendsto (fun r : ℝ => (Complex.exp (-I*k*r)*(r : ℂ)) • F (r • d))
      atTop (𝓝 A)) :
    Tendsto (fun r : ℝ => (Complex.exp (-I*(k/(s : ℂ))*r)*(r : ℂ)) •
      dilate s F (r • d)) atTop (𝓝 ((s : ℂ) • A)) := by
  have hr : Tendsto (fun r : ℝ => r/s) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop).const_mul_atTop (inv_pos.mpr hs)
  have ht := (tendsto_const_nhds (x := (s : ℂ))).smul (hF.comp hr)
  apply ht.congr'
  filter_upwards with r
  exact (scaled_ray_identity s hs k F r d).symm

theorem residue_far_limits_dilate (s : ℝ) (hs : 0 < s) (n k : ℂ) (hk : k ≠ 0)
    (f : Amplitudes) (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => (Complex.exp (-I*(k/(s : ℂ))*r)*(r : ℂ)) •
      dilate s (electricMode n k f) (r • d))
        atTop (𝓝 ((s : ℂ) • electricFar k (residue 1 n k f).2 d)) ∧
    Tendsto (fun r : ℝ => (Complex.exp (-I*(k/(s : ℂ))*r)*(r : ℂ)) •
      dilate s (magneticMode n k f) (r • d))
        atTop (𝓝 ((s : ℂ) • magneticFar k (residue 1 n k f).2 d)) :=
  ⟨dilate_ray_far_limit s hs k _ d _ (mode_electric_far_limit n k hk f d hd),
    dilate_ray_far_limit s hs k _ d _ (mode_magnetic_far_limit n k hk f d hd)⟩

theorem residue_far_nonzero_dilate (s : ℝ) (hs : 0 < s) (n : ℂ)
    (k : Frequency) (f : Amplitudes) (hf : residueOperator n k f ≠ 0) :
    ∃ d : Space, ‖d‖ = 1 ∧
      (s : ℂ) • electricFar k.1 (residue 1 n k.1 f).2 d ≠ 0 ∧
      (s : ℂ) • magneticFar k.1 (residue 1 n k.1 f).2 d ≠ 0 := by
  obtain ⟨d,hd,he,hh⟩ := nonzero_residue_far_field n k f hf
  exact ⟨d,hd,smul_ne_zero (ofReal_ne_zero.mpr hs.ne') he,
    smul_ne_zero (ofReal_ne_zero.mpr hs.ne') hh⟩

theorem sphereCoefficient_real_bounds (n : ℝ) (hn : 1 < n)
    (s : ℝ) (hs : 0 < s) (x : Space) :
    (sphereCoefficient (n : ℂ) s x).im = 0 ∧
      1 ≤ (sphereCoefficient (n : ℂ) s x).re ∧
      (sphereCoefficient (n : ℂ) s x).re ≤ n^2 := by
  rw [sphereCoefficient_dilate n s hs x]
  exact OQ14.ModalWeak.coefficient_real_bounds n hn _

theorem field_nonzero_of_far_limit (k : ℂ) (F : Field) (d : Space) (A : Vector)
    (hA : A ≠ 0)
    (hF : Tendsto (fun r : ℝ => (Complex.exp (-I*k*r)*(r : ℂ)) • F (r • d))
      atTop (𝓝 A)) : F ≠ 0 := by
  intro hz
  have hzero : Tendsto (fun r : ℝ => (Complex.exp (-I*k*r)*(r : ℂ)) • F (r • d))
      atTop (𝓝 0) := by simpa only [hz, Pi.zero_apply, smul_zero] using tendsto_const_nhds
  exact hA (tendsto_nhds_unique hF hzero)

theorem residue_dilated_fields_nonzero (s : ℝ) (hs : 0 < s) (n : ℂ)
    (k : Frequency) (f : Amplitudes) (hf : residueOperator n k f ≠ 0) :
    dilate s (electricMode n k.1 f) ≠ 0 ∧ dilate s (magneticMode n k.1 f) ≠ 0 := by
  obtain ⟨d,hd,he,hh⟩ := residue_far_nonzero_dilate s hs n k f hf
  obtain ⟨hE,hH⟩ := residue_far_limits_dilate s hs n k.1 k.property f d hd
  exact ⟨field_nonzero_of_far_limit _ _ d _ he hE,
    field_nonzero_of_far_limit _ _ d _ hh hH⟩

/-- The same actual high-quality residue mode, dilated to a positive sphere
radius, has prescribed positive real frequency and unchanged quality factor.
The simple shell-response pole recorded here is the original dimensionless
pole; no identification with a full Maxwell resolvent is made. -/
theorem exists_prescribed_frequency_modes (n : ℝ) (hn : 1 < n)
    (k0 : ℝ) (hk0 : 0 < k0) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : Frequency, ∃ f : Amplitudes, ∃ s : ℝ,
      0 < s ∧ (k.1/(s : ℂ)).re = k0 ∧ (k.1/(s : ℂ)).im < 0 ∧
      Q < (k.1/(s : ℂ)).re / (-2*(k.1/(s : ℂ)).im) ∧
      (∃ hm : MeromorphicAt (response (n : ℂ)) k.1, hm.order = (-1 : ℤ)) ∧
      residueOperator (n : ℂ) k f ≠ 0 ∧
      (dilate s (electricMode (n : ℂ) k.1 f) ≠ 0 ∧
        dilate s (magneticMode (n : ℂ) k.1 f) ≠ 0) ∧
      (∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        weakCurlPairing (dilate s (electricMode (n : ℂ) k.1 f)) φ =
          (fun j => ∫ x, (I*(k.1/(s : ℂ))*dilate s (magneticMode (n : ℂ) k.1 f) x j)*φ x) ∧
        weakCurlPairing (dilate s (magneticMode (n : ℂ) k.1 f)) φ =
          (fun j => ∫ x, (-I*(k.1/(s : ℂ))*sphereCoefficient (n : ℂ) s x*
            dilate s (electricMode (n : ℂ) k.1 f) x j)*φ x)) ∧
      (∀ (γ : ℝ → Space), Tendsto (fun t => ‖γ t‖) atTop atTop →
        Tendsto (fun t => dilatedRadiationDefect s (n : ℂ) k.1 f (γ t)) atTop (𝓝 0)) ∧
      (∃ d : Space, ‖d‖ = 1 ∧
        (s : ℂ) • electricFar k.1 (residue 1 (n : ℂ) k.1 f).2 d ≠ 0 ∧
        (s : ℂ) • magneticFar k.1 (residue 1 (n : ℂ) k.1 f).2 d ≠ 0 ∧
        Tendsto (fun r : ℝ => (Complex.exp (-I*(k.1/(s : ℂ))*r)*(r : ℂ)) •
          dilate s (electricMode (n : ℂ) k.1 f) (r • d))
            atTop (𝓝 ((s : ℂ) • electricFar k.1 (residue 1 (n : ℂ) k.1 f).2 d)) ∧
        Tendsto (fun r : ℝ => (Complex.exp (-I*(k.1/(s : ℂ))*r)*(r : ℂ)) •
          dilate s (magneticMode (n : ℂ) k.1 f) (r • d))
            atTop (𝓝 ((s : ℂ) • magneticFar k.1 (residue 1 (n : ℂ) k.1 f).2 d))) := by
  obtain ⟨k,f,hre,him,hQk,hpole,hf,_,hweak⟩ :=
    exists_high_quality_residue_modes n hn 0 Q hQ
  let s : ℝ := k.1.re/k0
  obtain ⟨hs,hsre,hsim,hsQ⟩ := prescribed_frequency_scale k.1 hre him k0 hk0
  refine ⟨k,f,s,hs,hsre,hsim,?_,hpole,hf,
    residue_dilated_fields_nonzero s hs (n : ℂ) k f hf, ?_,
    dilatedRadiationDefect_limit s hs (n : ℂ) k.1 k.property f, ?_⟩
  · rw [hsQ]
    exact hQk
  · exact weak_maxwell_dilate s hs (n : ℂ) k.1 _ _ hweak
  · obtain ⟨d,hd,he,hh⟩ := residue_far_nonzero_dilate s hs (n : ℂ) k f hf
    obtain ⟨hE,hH⟩ := residue_far_limits_dilate s hs (n : ℂ) k.1 k.property f d hd
    exact ⟨d,hd,he,hh,hE,hH⟩

end OQ14.ModalScaling

#print axioms OQ14.ModalScaling.dcoord_comp_smul
#print axioms OQ14.ModalScaling.curl_dilate
#print axioms OQ14.ModalScaling.dilated_test_contDiff
#print axioms OQ14.ModalScaling.dilated_test_compact
#print axioms OQ14.ModalScaling.integral_dilate_product
#print axioms OQ14.ModalScaling.integral_dilate_derivative
#print axioms OQ14.ModalScaling.weakCurlPairing_dilate
#print axioms OQ14.ModalScaling.sphereCoefficient_dilate
#print axioms OQ14.ModalScaling.weak_maxwell_dilate
#print axioms OQ14.ModalScaling.residue_weak_maxwell_dilate
#print axioms OQ14.ModalScaling.tangent_real_smul
#print axioms OQ14.ModalScaling.normalized_tangent_dilate
#print axioms OQ14.ModalScaling.dilatedRadiationDefect_eq
#print axioms OQ14.ModalScaling.dilatedRadiationDefect_limit
#print axioms OQ14.ModalScaling.frequency_dilate
#print axioms OQ14.ModalScaling.prescribed_frequency_scale
#print axioms OQ14.ModalScaling.scaled_ray_identity
#print axioms OQ14.ModalScaling.dilate_ray_far_limit
#print axioms OQ14.ModalScaling.residue_far_limits_dilate
#print axioms OQ14.ModalScaling.residue_far_nonzero_dilate
#print axioms OQ14.ModalScaling.sphereCoefficient_real_bounds
#print axioms OQ14.ModalScaling.field_nonzero_of_far_limit
#print axioms OQ14.ModalScaling.residue_dilated_fields_nonzero
#print axioms OQ14.ModalScaling.exists_prescribed_frequency_modes
