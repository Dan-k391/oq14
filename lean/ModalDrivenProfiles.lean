import ModalDrivenTrace
import ModalWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ModalDrivenProfiles
open Complex MeasureTheory Set Filter OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalProfiles
  OQ14.ModalOrigin OQ14.ModalInterface OQ14.ModalDriven OQ14.RadialInterface OQ14.ModalDipole
open scoped Topology

def outerA' (k b d z : ℂ) := outerA k b z + innerA 1 k d z
def outerB' (k b d z : ℂ) := outerB k b z + innerB 1 k d z
def outerC' (k b d z : ℂ) := outerC k b z + innerC 1 k d z
def outerP' (n k a b d z : ℂ) := outerP n k a b z + innerP 1 k d z - innerP 1 k d 1
def outerQ' (n k a b d z : ℂ) := outerA' k b d z - outerP' n k a b d z

theorem outerP'_match (n k a b d : ℂ) : innerP n k a 1 = outerP' n k a b d 1 := by
  simp only [outerP', add_sub_cancel_right]; exact potential_match n k a b

theorem outerP'_deriv (n k a b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    HasDerivAt (outerP' n k a b d) (z * outerB' k b d z) z := by
  have h := ((outerP_hasDerivAt n k a b z hk hz).add (innerP_hasDerivAt 1 k d z)).sub_const (innerP 1 k d 1)
  convert h using 1; simp only [outerP', outerB']; ring

theorem outerP'_differentiableAt (n k a b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerP' n k a b d) z := (outerP'_deriv n k a b d z hk hz).differentiableAt

theorem outerQ'_differentiableAt (n k a b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerQ' n k a b d) z := by
  unfold outerQ' outerA'
  exact ((outerA_differentiableAt k b z hk hz).add ((innerA_differentiable 1 k d) z)).sub
    (outerP'_differentiableAt n k a b d z hk hz)

theorem outerC'_differentiableAt (k b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerC' k b d) z := by
  exact (outerC_differentiableAt k b z hk hz).add ((innerC_differentiable 1 k d) z)

theorem profiles_match (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    innerA n k (numerator n k).1 1 = outerA' k (numerator n k).2 (determinant n k) 1 ∧
    innerC n k (numerator n k).1 1 = outerC' k (numerator n k).2 (determinant n k) 1 ∧
    innerQ n k (numerator n k).1 1 = outerQ' n k (numerator n k).1 (numerator n k).2 (determinant n k) 1 := by
  have hE := congrArg Prod.snd (numerator_matching n k)
  have hH := congrArg Prod.fst (numerator_matching n k)
  change psiD 1 (n*k) * (numerator n k).1 - xiD 1 k * (numerator n k).2 = determinant n k * psiD 1 k at hE
  change n * psi 1 (n*k) * (numerator n k).1 - xi 1 k * (numerator n k).2 = determinant n k * psi 1 k at hH
  have he : innerA n k (numerator n k).1 1 = outerA' k (numerator n k).2 (determinant n k) 1 := by
    rw [innerA_one n k _ hn hk, outerA', innerA_one 1 k _ one_ne_zero hk]
    simp only [outerA, mul_one, div_one, one_mul]
    linear_combination k*hE
  have hh : innerC n k (numerator n k).1 1 = outerC' k (numerator n k).2 (determinant n k) 1 := by
    rw [innerC_one n k _ hn hk, outerC', innerC_one 1 k _ one_ne_zero hk]
    simp only [outerC, mul_one, one_pow, div_one, one_mul]
    linear_combination (I*k)*hH
  exact ⟨he, hh, by simp only [innerQ, outerQ']; rw [he, ← outerP'_match]⟩

def potentialGradient (n k a b d : ℂ) : Field := fun x i =>
  radialCoordinateD (fun r => innerP n k a r) (fun r => outerP' n k a b d r)
    (fun r => deriv (innerP n k a) r) (fun r => deriv (outerP' n k a b d) r) i 2 x

def axial (n k a b d : ℂ) : Field := fun x =>
  ![0,0,radial (fun r => innerQ n k a r) (fun r => outerQ' n k a b d r) x]

theorem potentialGradient_weak_curl_zero (n k a b d : ℂ) (hk : k ≠ 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (potentialGradient n k a b d) φ = 0 := by
  have hi := entire_real_profile _ (innerP_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerP'_differentiableAt n k a b d z hk hz)
  exact radialCoordinate_gradient_curl_zero _ _ _ _ hi.1 ho.1 (by simpa using outerP'_match n k a b d)
    (fun r _ => hi.2.2 r) ho.2.2 hi.2.1 ho.2.1 2 φ hφ hc

theorem axial_continuous (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (i : Fin 3) :
    Continuous (fun x => axial n k (numerator n k).1 (numerator n k).2 (determinant n k) x i) := by
  have hi := entire_real_profile _ (innerQ_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerQ'_differentiableAt n k (numerator n k).1 (numerator n k).2 (determinant n k) z hk hz)
  have hc := radial_continuous _ _ hi.1 ho.1 (by simpa using (profiles_match n k hn hk).2.2)
  fin_cases i <;> simp only [axial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]
  · exact continuous_const
  · exact continuous_const
  · exact hc

theorem electric_profiles (n k : ℂ) (x : Space) :
    OQ14.ModalDriven.electric n k x =
      ![radial (fun r => innerB n k (numerator n k).1 r) (fun r => outerB' k (numerator n k).2 (determinant n k) r) x * (x 2 : ℂ) * (x 0 : ℂ),
        radial (fun r => innerB n k (numerator n k).1 r) (fun r => outerB' k (numerator n k).2 (determinant n k) r) x * (x 2 : ℂ) * (x 1 : ℂ),
        radial (fun r => innerA n k (numerator n k).1 r) (fun r => outerA' k (numerator n k).2 (determinant n k) r) x +
          radial (fun r => innerB n k (numerator n k).1 r) (fun r => outerB' k (numerator n k).2 (determinant n k) r) x * (x 2 : ℂ) * (x 2 : ℂ)] := by
  unfold OQ14.ModalDriven.electric radial
  split_ifs <;> ext j <;> fin_cases j <;>
    simp [centerE, innerA, innerB, outerA', outerB', outgoingE, dipoleE, axisField,
      outerA, outerB, electricA, electricB, scaledRadial, scaledRadialD, div_eq_mul_inv] <;> ring

theorem potentialGradient_formula (n k a b d : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    potentialGradient n k a b d x i =
      radial (fun r => innerP n k a r) (fun r => outerP' n k a b d r) x *
        (if i = 2 then 1 else 0) +
      radial (fun r => innerB n k a r) (fun r => outerB' k b d r) x * (x 2 : ℂ) * (x i : ℂ) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  unfold potentialGradient radialCoordinateD radialD radial
  dsimp only
  rw [(innerP_hasDerivAt n k a (‖x‖ : ℂ)).deriv,
    (outerP'_deriv n k a b d (‖x‖ : ℂ) hk hr).deriv]
  split_ifs <;> push_cast <;> field_simp [hr] <;> ring

theorem electric_decomposition (n k : ℂ) (hk : k ≠ 0) (x : Space) (hx : x ≠ 0) :
    OQ14.ModalDriven.electric n k x = fun i =>
      potentialGradient n k (numerator n k).1 (numerator n k).2 (determinant n k) x i +
      axial n k (numerator n k).1 (numerator n k).2 (determinant n k) x i := by
  rw [electric_profiles]
  have hq : radial (fun r => innerQ n k (numerator n k).1 r)
      (fun r => outerQ' n k (numerator n k).1 (numerator n k).2 (determinant n k) r) x =
      radial (fun r => innerA n k (numerator n k).1 r) (fun r => outerA' k (numerator n k).2 (determinant n k) r) x -
      radial (fun r => innerP n k (numerator n k).1 r) (fun r => outerP' n k (numerator n k).1 (numerator n k).2 (determinant n k) r) x := by
    unfold radial innerQ outerQ'
    split_ifs <;> rfl
  ext i
  rw [potentialGradient_formula n k _ _ _ hk x hx]
  fin_cases i <;> simp [axial, hq]
  ring

theorem magnetic_profiles (n k : ℂ) (hk : k ≠ 0) (x : Space) :
    OQ14.ModalDriven.magnetic n k x =
      ![radial (fun r => innerC n k (numerator n k).1 r) (fun r => outerC' k (numerator n k).2 (determinant n k) r) x * (x 1 : ℂ),
        -radial (fun r => innerC n k (numerator n k).1 r) (fun r => outerC' k (numerator n k).2 (determinant n k) r) x * (x 0 : ℂ),0] := by
  have hkk : I*k^2/k = I*k := by field_simp [hk]; ring
  unfold OQ14.ModalDriven.magnetic radial
  split_ifs <;> ext j <;> fin_cases j <;>
    simp [centerH, innerC, outerC', outgoingH, dipoleH, swirlField,
      outerC, magneticC, scaledRadial, hkk]
  all_goals (simp only [div_eq_mul_inv]; ring)

theorem magnetic_continuous (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (i : Fin 3) :
    Continuous (fun x => OQ14.ModalDriven.magnetic n k x i) := by
  have hi := entire_real_profile _ (innerC_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerC'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)
  have hc := radial_continuous _ _ hi.1 ho.1 (by simpa using (profiles_match n k hn hk).2.1)
  have hform := funext (magnetic_profiles n k hk)
  rw [hform]
  fin_cases i
  · exact hc.mul (coordinate 1).continuous
  · exact hc.neg.mul (coordinate 0).continuous
  · exact continuous_const

theorem potentialGradient_locallyIntegrable (n k a b d : ℂ) (hk : k ≠ 0) (i : Fin 3) :
    LocallyIntegrable (fun x => potentialGradient n k a b d x i) := by
  have hi := entire_real_profile _ (innerP_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerP'_differentiableAt n k a b d z hk hz)
  exact radialCoordinateD_locallyIntegrable _ _ _ _ hi.1 ho.1 (by simpa using outerP'_match n k a b d)
    hi.2.1 ho.2.1 i 2

theorem electric_weakCurl_eq_axial (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (OQ14.ModalDriven.electric n k) φ =
      weakCurlPairing (axial n k (numerator n k).1 (numerator n k).2 (determinant n k)) φ := by
  have he : OQ14.ModalDriven.electric n k =ᵐ[volume]
      (fun x i => potentialGradient n k (numerator n k).1 (numerator n k).2 (determinant n k) x i +
        axial n k (numerator n k).1 (numerator n k).2 (determinant n k) x i) := by
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    exact electric_decomposition n k hk x hx
  rw [OQ14.ModalWeak.weakCurlPairing_congr_ae _ _ he, OQ14.ModalWeak.weakCurlPairing_add _ _
    (potentialGradient_locallyIntegrable n k _ _ _ hk)
    (fun i => (axial_continuous n k hn hk i).locallyIntegrable)
    φ (hφ.of_le (by norm_num)) hc,
    potentialGradient_weak_curl_zero n k _ _ _ hk φ hφ hc]
  ext i
  simp

theorem axial_differentiableAt (n k : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => axial n k (numerator n k).1 (numerator n k).2 (determinant n k) y i) x := by
  have hi := entire_real_profile _ (innerQ_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerQ'_differentiableAt n k (numerator n k).1 (numerator n k).2 (determinant n k) z hk hz)
  have h := radial_differentiableAt _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 x hx0 hx1
  fin_cases i
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact h

theorem axial_partial_locallyIntegrable (n k : ℂ) (hk : k ≠ 0) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (axial n k (numerator n k).1 (numerator n k).2 (determinant n k)) x i j) := by
  have hi := entire_real_profile _ (innerQ_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerQ'_differentiableAt n k (numerator n k).1 (numerator n k).2 (determinant n k) z hk hz)
  have h := radial_dcoord_locallyIntegrable _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 hi.2.1 ho.2.1 i
  fin_cases j <;> dsimp [pd, axial]
  · simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))
  · simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))
  · exact h

theorem magnetic_differentiableAt (n k : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => OQ14.ModalDriven.magnetic n k y i) x := by
  have hi := entire_real_profile _ (innerC_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerC'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)
  have h := radial_differentiableAt _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 x hx0 hx1
  rw [funext (magnetic_profiles n k hk)]
  fin_cases i
  · exact h.mul (coordinate_differentiableAt x 1)
  · exact h.neg.mul (coordinate_differentiableAt x 0)
  · exact differentiableAt_const _

theorem magnetic_partial_locallyIntegrable (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (i j : Fin 3) :
    LocallyIntegrable (fun x => pd (OQ14.ModalDriven.magnetic n k) x i j) := by
  have hi := entire_real_profile _ (innerC_differentiable n k (numerator n k).1)
  have ho := punctured_real_profile _ (fun z hz => outerC'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)
  have he := (profiles_match n k hn hk).2.1
  have h (m : Fin 3) := radial_coordinate_dcoord_locallyIntegrable _ _ _ _
    hi.1 ho.1 (by simpa using he) (fun r _ => hi.2.2 r) ho.2.2 hi.2.1 ho.2.1 i m
  have he0 : (fun x => OQ14.ModalDriven.magnetic n k x 0) =
      (fun x => radial (fun r => innerC n k (numerator n k).1 r) (fun r => outerC' k (numerator n k).2 (determinant n k) r) x * (x 1 : ℂ)) := by
    funext x; rw [magnetic_profiles n k hk]; rfl
  have he1 : (fun x => OQ14.ModalDriven.magnetic n k x 1) =
      (fun x => -(radial (fun r => innerC n k (numerator n k).1 r) (fun r => outerC' k (numerator n k).2 (determinant n k) r) x * (x 0 : ℂ))) := by
    funext x; rw [magnetic_profiles n k hk]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, neg_mul]
  have he2 : (fun x => OQ14.ModalDriven.magnetic n k x 2) = (fun _ : Space => (0 : ℂ)) := by
    funext x; rw [magnetic_profiles n k hk]; rfl
  fin_cases j <;> dsimp [pd]
  · rw [he0]; exact h 1
  · rw [he1]; exact OQ14.ModalWeak.partial_neg_locallyIntegrable _ i (h 0)
  · rw [he2]; simp only [dcoord, fderiv_const, ContinuousLinearMap.zero_apply]
    exact (locallyIntegrable_zero : LocallyIntegrable (fun _ : Space => (0 : ℂ)))

def potential (n k a b d : ℂ) (x : Space) : ℂ :=
  radial (fun r => innerP n k a r) (fun r => outerP' n k a b d r) x * (x 2 : ℂ)

theorem potential_contDiffAt (n k a b d : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    ContDiffAt ℝ 2 (potential n k a b d) x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx0)
  have hn : ContDiffAt ℝ 2 (fun y : Space => (‖y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx0)
  rcases hx1.lt_or_lt with hx | hx
  · have hi : ContDiffAt ℝ 2 (fun y : Space => innerP n k a (‖y‖ : ℂ) * (y 2 : ℂ)) x :=
      (((innerP_differentiable n k a).contDiff.restrict_scalars ℝ).contDiffAt.comp x hn).mul
        (coordinate 2).contDiff.contDiffAt
    apply hi.congr_of_eventuallyEq
    exact (radial_eventually_inner (fun r => innerP n k a r)
      (fun r => outerP' n k a b d r) x hx).mul EventuallyEq.rfl
  · have hhol : DifferentiableOn ℂ (outerP' n k a b d) {z | z ≠ 0} :=
      fun z hz => (outerP'_differentiableAt n k a b d z hk hz).differentiableWithinAt
    have ho : ContDiffAt ℂ 2 (outerP' n k a b d) (‖x‖ : ℂ) :=
      (hhol.analyticOnNhd isOpen_ne _ hr).contDiffAt
    have horeal : ContDiffAt ℝ 2 (outerP' n k a b d) (‖x‖ : ℂ) := ho.restrict_scalars ℝ
    have hop : ContDiffAt ℝ 2 (fun y : Space => outerP' n k a b d (‖y‖ : ℂ)) x :=
      ContDiffAt.comp (g := outerP' n k a b d) (f := fun y : Space => (‖y‖ : ℂ)) x horeal hn
    have hh : ContDiffAt ℝ 2 (fun y : Space => outerP' n k a b d (‖y‖ : ℂ) * (y 2 : ℂ)) x :=
      hop.mul (coordinate 2).contDiff.contDiffAt
    apply hh.congr_of_eventuallyEq
    exact (radial_eventually_outer (fun r => innerP n k a r)
      (fun r => outerP' n k a b d r) x hx).mul EventuallyEq.rfl

theorem potential_actual_partial (n k a b d : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    dcoord (potential n k a b d) x i = potentialGradient n k a b d x i := by
  have hi := entire_real_profile _ (innerP_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerP'_differentiableAt n k a b d z hk hz)
  exact radial_coordinate_partial _ _ _ _ (fun r _ => hi.2.2 r) ho.2.2 x hx0 hx1 i 2

theorem potentialGradient_eventually (n k a b d : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    potentialGradient n k a b d =ᶠ[𝓝 x] gradient (potential n k a b d) := by
  have hn : {y : Space | ‖y‖ ≠ 1} ∈ 𝓝 x :=
    (isOpen_ne.preimage continuous_norm).mem_nhds hx1
  filter_upwards [isOpen_ne.mem_nhds hx0, hn] with y hy0 hy1
  ext i
  exact (potential_actual_partial n k a b d hk y hy0 hy1 i).symm

theorem potentialGradient_differentiableAt (n k a b d : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => potentialGradient n k a b d y i) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (potential n k a b d)) x :=
    (potential_contDiffAt n k a b d hk x hx0 hx1).fderiv_right (by norm_num)
  have h := (hd.differentiableAt le_rfl).clm_apply (differentiableAt_const (basis i))
  exact h.congr_of_eventuallyEq
    ((potentialGradient_eventually n k a b d hk x hx0 hx1).fun_comp (fun v => v i))

theorem electric_curl_eq_axial (n k : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    curl (OQ14.ModalDriven.electric n k) x = curl (axial n k (numerator n k).1 (numerator n k).2 (determinant n k)) x := by
  have he : OQ14.ModalDriven.electric n k =ᶠ[𝓝 x]
      (fun y i => potentialGradient n k (numerator n k).1 (numerator n k).2 (determinant n k) y i +
        axial n k (numerator n k).1 (numerator n k).2 (determinant n k) y i) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact electric_decomposition n k hk y hy
  rw [curl_eventuallyEq _ _ x he, curl_add _ _ x
    (potentialGradient_differentiableAt n k _ _ _ hk x hx0 hx1)
    (axial_differentiableAt n k hk x hx0 hx1),
    curl_eventuallyEq _ _ x (potentialGradient_eventually n k _ _ _ hk x hx0 hx1),
    OQ14.ModalWeak.curl_gradient_at _ x (potential_contDiffAt n k _ _ _ hk x hx0 hx1)]
  ext i; simp

#print axioms OQ14.ModalDrivenProfiles.electric_curl_eq_axial
#print axioms OQ14.ModalDrivenProfiles.magnetic_partial_locallyIntegrable
#print axioms OQ14.ModalDrivenProfiles.electric_weakCurl_eq_axial
#print axioms OQ14.ModalDrivenProfiles.magnetic_continuous
#print axioms OQ14.ModalDrivenProfiles.electric_decomposition
#print axioms OQ14.ModalDrivenProfiles.profiles_match
#print axioms OQ14.ModalDrivenProfiles.potentialGradient_weak_curl_zero
#print axioms OQ14.ModalDrivenProfiles.axial_continuous
end OQ14.ModalDrivenProfiles









