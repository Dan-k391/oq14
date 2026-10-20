import ModalProfiles

/-!
# The actual assembled weak spherical Maxwell field

The normal electric jump is handled by the proved potential decomposition.
All remaining fields are continuous and have locally integrable actual
derivatives, so their distributional curls follow from interface calculus.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OQ14.ModalWeak

open Complex MeasureTheory Set Filter OQ14.Maxwell OQ14.ModalProfiles OQ14.ModalOrigin
  OQ14.ModalInterface OQ14.ModalDipole OQ14.ModalMatching OQ14.RadialInterface
open scoped Topology

theorem curl_gradient_at (f : Space → ℂ) (x : Space) (hf : ContDiffAt ℝ 2 f x) :
    curl (gradient f) x = 0 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hp (i j : Fin 3) :
      dcoord (fun y => dcoord f y j) x i =
        fderiv ℝ (fderiv ℝ f) x (basis i) (basis j) := by
    simp [dcoord, fderiv_clm_apply (hd.differentiableAt le_rfl) (differentiableAt_const (basis j))]
  have hc (i j : Fin 3) :
      dcoord (fun y => dcoord f y j) x i = dcoord (fun y => dcoord f y i) x j := by
    rw [hp, hp]
    exact hf.isSymmSndFDerivAt (by norm_num) (basis i) (basis j)
  ext j
  fin_cases j <;> simp [curl, gradient, pd, hc]

theorem potential_contDiffAt (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    ContDiffAt ℝ 2 (potential n k a b) x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0)
  have hn : ContDiffAt ℝ 2 (fun y : Space => (‖y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx0)
  rcases hx1.lt_or_lt with hx | hx
  · have hi : ContDiffAt ℝ 2 (fun y : Space => innerP n k a (‖y‖ : ℂ) * (y 2 : ℂ)) x :=
      (((innerP_differentiable n k a).contDiff.restrict_scalars ℝ).contDiffAt.comp x hn).mul
        (coordinate 2).contDiff.contDiffAt
    apply hi.congr_of_eventuallyEq
    exact (radial_eventually_inner (fun r => innerP n k a r)
      (fun r => outerP n k a b r) x hx).mul EventuallyEq.rfl
  · have hhol : DifferentiableOn ℂ (outerP n k a b) {z | z ≠ 0} :=
      fun z hz => (outerP_differentiableAt n k a b z hk hz).differentiableWithinAt
    have ho : ContDiffAt ℂ 2 (outerP n k a b) (‖x‖ : ℂ) :=
      (hhol.analyticOnNhd isOpen_ne _ hr).contDiffAt
    have horeal : ContDiffAt ℝ 2 (outerP n k a b) (‖x‖ : ℂ) := ho.restrict_scalars ℝ
    have hop : ContDiffAt ℝ 2 (fun y : Space => outerP n k a b (‖y‖ : ℂ)) x :=
      ContDiffAt.comp (g := outerP n k a b) (f := fun y : Space => (‖y‖ : ℂ)) x horeal hn
    have hh : ContDiffAt ℝ 2 (fun y : Space => outerP n k a b (‖y‖ : ℂ) * (y 2 : ℂ)) x :=
      hop.mul (coordinate 2).contDiff.contDiffAt
    apply hh.congr_of_eventuallyEq
    exact (radial_eventually_outer (fun r => innerP n k a r)
      (fun r => outerP n k a b r) x hx).mul EventuallyEq.rfl

theorem potentialGradient_eventually (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    potentialGradient n k a b =ᶠ[𝓝 x] gradient (potential n k a b) := by
  have hn : {y : Space | ‖y‖ ≠ 1} ∈ 𝓝 x :=
    (isOpen_ne.preimage continuous_norm).mem_nhds hx1
  filter_upwards [isOpen_ne.mem_nhds hx0, hn] with y hy0 hy1
  ext i
  exact (potential_actual_partial n k a b hk y hy0 hy1 i).symm

theorem potentialGradient_differentiableAt (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => potentialGradient n k a b y i) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (potential n k a b)) x :=
    (potential_contDiffAt n k a b hk x hx0 hx1).fderiv_right (by norm_num)
  have h := (hd.differentiableAt le_rfl).clm_apply (differentiableAt_const (basis i))
  exact h.congr_of_eventuallyEq
    ((potentialGradient_eventually n k a b hk x hx0 hx1).fun_comp (fun v => v i))

theorem potentialGradient_classical_curl_zero (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    curl (potentialGradient n k a b) x = 0 := by
  rw [curl_eventuallyEq _ _ x (potentialGradient_eventually n k a b hk x hx0 hx1)]
  exact curl_gradient_at _ x (potential_contDiffAt n k a b hk x hx0 hx1)

theorem axial_differentiableAt (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => axial n k a b y i) x := by
  have hi := entire_real_profile _ (innerQ_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerQ_differentiableAt n k a b z hk hz)
  have h := radial_differentiableAt _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 x hx0 hx1
  fin_cases i
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact h

theorem electric_curl_eq_axial (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    curl (electric n k a b) x = curl (axial n k a b) x := by
  have he : electric n k a b =ᶠ[𝓝 x]
      (fun y i => potentialGradient n k a b y i + axial n k a b y i) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact electric_decomposition n k a b hk y hy
  rw [curl_eventuallyEq _ _ x he, curl_add _ _ x
    (potentialGradient_differentiableAt n k a b hk x hx0 hx1)
    (axial_differentiableAt n k a b hk x hx0 hx1),
    potentialGradient_classical_curl_zero n k a b hk x hx0 hx1]
  ext i
  simp

theorem axial_partial_locallyIntegrable (n k a b : ℂ) (hk : k ≠ 0) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (axial n k a b) x i j) := by
  have hi := entire_real_profile _ (innerQ_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerQ_differentiableAt n k a b z hk hz)
  have h := radial_dcoord_locallyIntegrable _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 hi.2.1 ho.2.1 i
  fin_cases j <;> dsimp [pd, axial]
  ·
    simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))
  ·
    simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))
  · exact h

theorem magnetic_differentiableAt (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => magnetic n k a b y i) x := by
  have hi := entire_real_profile _ (innerC_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerC_differentiableAt k b z hk hz)
  have h := radial_differentiableAt _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 x hx0 hx1
  rw [funext (magnetic_profiles n k a b hk)]
  fin_cases i
  · exact h.mul (coordinate_differentiableAt x 1)
  · exact h.neg.mul (coordinate_differentiableAt x 0)
  · exact differentiableAt_const _

theorem partial_neg_locallyIntegrable (f : Space → ℂ) (i : Fin 3)
    (h : LocallyIntegrable (fun x => dcoord f x i)) :
    LocallyIntegrable (fun x => dcoord (fun y => -f y) x i) := by
  simpa only [dcoord, fderiv_neg, ContinuousLinearMap.neg_apply, Pi.neg_apply] using h.neg

theorem magnetic_partial_locallyIntegrable (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (magnetic n k a b) x i j) := by
  have hi := entire_real_profile _ (innerC_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerC_differentiableAt k b z hk hz)
  have he := (profiles_match n k a b hn hk hm).2.1
  have h (m : Fin 3) := radial_coordinate_dcoord_locallyIntegrable _ _ _ _
    hi.1 ho.1 (by simpa using he) (fun r _ => hi.2.2 r) ho.2.2 hi.2.1 ho.2.1 i m
  have he0 : (fun x => magnetic n k a b x 0) =
      (fun x => radial (fun r => innerC n k a r) (fun r => outerC k b r) x * (x 1 : ℂ)) := by
    funext x
    rw [magnetic_profiles n k a b hk]
    rfl
  have he1 : (fun x => magnetic n k a b x 1) =
      (fun x => -(radial (fun r => innerC n k a r) (fun r => outerC k b r) x * (x 0 : ℂ))) := by
    funext x
    rw [magnetic_profiles n k a b hk]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, neg_mul]
  have he2 : (fun x => magnetic n k a b x 2) = (fun _ : Space => (0 : ℂ)) := by
    funext x
    rw [magnetic_profiles n k a b hk]
    rfl
  fin_cases j <;> dsimp [pd]
  ·
    rw [he0]
    exact h 1
  ·
    rw [he1]
    exact partial_neg_locallyIntegrable _ i (h 0)
  ·
    rw [he2]
    simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))

theorem weakCurlPairing_congr_ae (E F : Field) (he : E =ᵐ[volume] F) (φ : Space → ℂ) :
    weakCurlPairing E φ = weakCurlPairing F φ := by
  have hp (i j : Fin 3) :
      (∫ x, E x i * dcoord φ x j) = ∫ x, F x i * dcoord φ x j := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  ext j
  fin_cases j <;> simp only [weakCurlPairing, hp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]

theorem weakCurlPairing_add (E F : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (fun x i => E x i + F x i) φ =
      fun i => weakCurlPairing E φ i + weakCurlPairing F φ i := by
  have hI (G : Field) (hG : ∀ i, LocallyIntegrable (fun x => G x i)) (i j : Fin 3) :
      Integrable (fun x => G x i * dcoord φ x j) := by
    have hjc : Continuous (fun x => dcoord φ x j) := partial_continuous hφ j
    have hjk : HasCompactSupport (fun x => dcoord φ x j) := hc.fderiv_apply ℝ (basis j)
    exact OQ14.PointSingularity.test_product_integrable
      (fun x => G x i) (fun x => dcoord φ x j) (hG i) hjc hjk
  have hp (i j : Fin 3) :
      (∫ x, (E x i + F x i) * dcoord φ x j) =
        (∫ x, E x i * dcoord φ x j) + ∫ x, F x i * dcoord φ x j := by
    simp_rw [add_mul]
    exact integral_add (hI E hE i j) (hI F hF i j)
  ext i
  fin_cases i <;> dsimp [weakCurlPairing] <;> rw [hp, hp] <;> ring

theorem electric_weakCurl_eq_axial (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (electric n k a b) φ = weakCurlPairing (axial n k a b) φ := by
  have he : electric n k a b =ᵐ[volume]
      (fun x i => potentialGradient n k a b x i + axial n k a b x i) := by
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    exact electric_decomposition n k a b hk x hx
  rw [weakCurlPairing_congr_ae _ _ he, weakCurlPairing_add _ _
    (potentialGradient_locallyIntegrable n k a b hk)
    (fun i => (axial_continuous n k a b hn hk hm i).locallyIntegrable)
    φ (hφ.of_le (by norm_num)) hc,
    potentialGradient_weak_curl_zero n k a b hk φ hφ hc]
  ext i
  simp

theorem electric_locallyIntegrable (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0) (i : Fin 3) :
    LocallyIntegrable (fun x => electric n k a b x i) := by
  have hloc := (potentialGradient_locallyIntegrable n k a b hk i).add
    (axial_continuous n k a b hn hk hm i).locallyIntegrable
  have he : (fun x => electric n k a b x i) =ᵐ[volume]
      (fun x => potentialGradient n k a b x i + axial n k a b x i) := by
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    exact congrFun (electric_decomposition n k a b hk x hx) i
  exact hloc.mono (hloc.aestronglyMeasurable.congr he.symm)
    (he.mono (fun _ hx => le_of_eq (congrArg norm hx)))

/-- Actual global distributional Maxwell equations for the assembled field,
with the interface contribution discharged from its explicit profiles. -/
theorem assembled_weak_maxwell (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (electric n k a b) φ =
      (fun j => ∫ x, (I*k*magnetic n k a b x j)*φ x) ∧
    weakCurlPairing (magnetic n k a b) φ =
      (fun j => ∫ x, (-I*k*coefficient n x*electric n k a b x j)*φ x) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  constructor
  · rw [electric_weakCurl_eq_axial n k a b hn hk hm φ hφ hc,
      ← OQ14.RadialInterface.curl_integration_by_parts 1 _ (axial_continuous n k a b hn hk hm)
        (axial_differentiableAt n k a b hk) (axial_partial_locallyIntegrable n k a b hk) φ hφ1 hc]
    ext j
    apply integral_congr_ae
    filter_upwards [ae_regular 1] with x hx
    rw [← electric_curl_eq_axial n k a b hk x hx.1 hx.2,
      (assembled_classical_maxwell n k a b hn hk x hx.2).1]
  · rw [← OQ14.RadialInterface.curl_integration_by_parts 1 _
      (magnetic_continuous n k a b hn hk hm) (magnetic_differentiableAt n k a b hk)
      (magnetic_partial_locallyIntegrable n k a b hn hk hm) φ hφ1 hc]
    ext j
    apply integral_congr_ae
    filter_upwards [ae_regular 1] with x hx
    rw [(assembled_classical_maxwell n k a b hn hk x hx.2).2]

theorem displacement_locallyIntegrable (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0) (i : Fin 3) :
    LocallyIntegrable (fun x => coefficient n x * electric n k a b x i) := by
  let s : Set Space := {x | ‖x‖ ≤ 1}
  have hs : MeasurableSet s := measurableSet_le continuous_norm.measurable measurable_const
  have he : (fun x => coefficient n x * electric n k a b x i) =
      (n^2) • s.indicator (fun x => electric n k a b x i) +
        sᶜ.indicator (fun x => electric n k a b x i) := by
    funext x
    by_cases hx : ‖x‖ ≤ 1 <;> simp [coefficient, s, hx]
  rw [he]
  have hE := electric_locallyIntegrable n k a b hn hk hm i
  exact ((hE.indicator hs).smul (n^2)).add (hE.indicator hs.compl)

theorem assembled_boundary_trace (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0) (x : Space) (hx : ‖x‖ = 1) :
    tangent x (electric n k a b x) = tangent x (outerE k b x) ∧
      tangent x (magnetic n k a b x) = tangent x (outerH k b x) := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hma : matching 1 n (k * (1 : ℝ)) (a,b) = 0 := by simpa using hm
  have hmatch := matching_implies_sphere_matches n k hn hk 1 (a,b) hma x hx
  simpa only [electric, magnetic, hx, le_refl, if_true,
    entireInnerE_eq n k a hn hk x hx0, entireInnerH_eq n k a hn hk x hx0] using hmatch

theorem assembled_exterior (n k a b : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    electric n k a b x = outerE k b x ∧ magnetic n k a b x = outerH k b x := by
  simp only [electric, magnetic, not_le.mpr hx, if_false, and_self]

theorem coefficient_real_bounds (n : ℝ) (hn : 1 < n) (x : Space) :
    (coefficient (n : ℂ) x).im = 0 ∧
      1 ≤ (coefficient (n : ℂ) x).re ∧
      (coefficient (n : ℂ) x).re ≤ n^2 := by
  have hsq : (1 : ℝ) ≤ n^2 := by nlinarith
  by_cases hx : ‖x‖ ≤ 1 <;> simp [coefficient, hx, ← ofReal_pow, hsq]

/-- Existence uses the previously proved actual determinant zeros and actual
interface matching. The fields here satisfy global weak Maxwell equations;
no interface or distributional equation is assumed in this conclusion.
The separate identification with a full Maxwell resolvent pole is not asserted. -/
theorem exists_high_quality_weak_fields (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k a b : ℂ, k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ L < k.re ∧ k.im < 0 ∧
      Q < k.re / (-2 * k.im) ∧
      (∀ i : Fin 3,
        LocallyIntegrable (fun x => electric (n : ℂ) k a b x i) ∧
        LocallyIntegrable (fun x => magnetic (n : ℂ) k a b x i) ∧
        LocallyIntegrable (fun x => coefficient (n : ℂ) x * electric (n : ℂ) k a b x i)) ∧
      (∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        weakCurlPairing (electric (n : ℂ) k a b) φ =
          (fun j => ∫ x, (I*k*magnetic (n : ℂ) k a b x j)*φ x) ∧
        weakCurlPairing (magnetic (n : ℂ) k a b) φ =
          (fun j => ∫ x, (-I*k*coefficient (n : ℂ) x*electric (n : ℂ) k a b x j)*φ x)) ∧
      (∃ x : Space, ‖x‖ = 1 ∧
        (tangent x (electric (n : ℂ) k a b x) ≠ 0 ∨
          tangent x (magnetic (n : ℂ) k a b x) ≠ 0)) ∧
      (∀ x : Space, 1 < ‖x‖ →
        electric (n : ℂ) k a b x = outerE k b x ∧
          magnetic (n : ℂ) k a b x = outerH k b x) := by
  obtain ⟨k, a, b, hk, ha, hb, hL, hi, hratio, hmatch, -, -, x, hx, htrace⟩ :=
    exists_high_quality_transmission_fields n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hm : matching 1 (n : ℂ) k (a,b) = 0 := by
    simpa using sphere_matches_implies_matching (n : ℂ) k hn0 hk 1 (by norm_num) (a,b) hmatch
  refine ⟨k, a, b, hk, ha, hb, hL, hi, hratio, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨electric_locallyIntegrable _ _ _ _ hn0 hk hm i,
      (magnetic_continuous _ _ _ _ hn0 hk hm i).locallyIntegrable,
      displacement_locallyIntegrable _ _ _ _ hn0 hk hm i⟩
  · exact assembled_weak_maxwell _ _ _ _ hn0 hk hm
  · refine ⟨x, hx, ?_⟩
    have ht := assembled_boundary_trace _ _ _ _ hn0 hk hm x hx
    rwa [ht.1, ht.2]
  · exact assembled_exterior _ _ _ _

end OQ14.ModalWeak

#print axioms OQ14.ModalWeak.curl_gradient_at
#print axioms OQ14.ModalWeak.potential_contDiffAt
#print axioms OQ14.ModalWeak.potentialGradient_eventually
#print axioms OQ14.ModalWeak.potentialGradient_differentiableAt
#print axioms OQ14.ModalWeak.potentialGradient_classical_curl_zero
#print axioms OQ14.ModalWeak.axial_differentiableAt
#print axioms OQ14.ModalWeak.electric_curl_eq_axial
#print axioms OQ14.ModalWeak.axial_partial_locallyIntegrable
#print axioms OQ14.ModalWeak.magnetic_differentiableAt
#print axioms OQ14.ModalWeak.partial_neg_locallyIntegrable
#print axioms OQ14.ModalWeak.magnetic_partial_locallyIntegrable
#print axioms OQ14.ModalWeak.weakCurlPairing_congr_ae
#print axioms OQ14.ModalWeak.weakCurlPairing_add
#print axioms OQ14.ModalWeak.electric_weakCurl_eq_axial
#print axioms OQ14.ModalWeak.electric_locallyIntegrable
#print axioms OQ14.ModalWeak.assembled_weak_maxwell
#print axioms OQ14.ModalWeak.displacement_locallyIntegrable
#print axioms OQ14.ModalWeak.assembled_boundary_trace
#print axioms OQ14.ModalWeak.assembled_exterior
#print axioms OQ14.ModalWeak.coefficient_real_bounds
#print axioms OQ14.ModalWeak.exists_high_quality_weak_fields
