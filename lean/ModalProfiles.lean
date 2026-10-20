import RadialInterface
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual scalar profiles of the spherical Maxwell mode

The potential profile is chosen so that its radial derivative is exactly
radius times the normal electric coefficient. Its exterior additive constant
makes the potential continuous without changing its gradient.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalProfiles

open Complex OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalWronskian
  OQ14.ModalDipole OQ14.ModalInterface OQ14.ModalOrigin OQ14.RadialInterface
  MeasureTheory Set Filter
open scoped Topology

def innerA (n k a z : ℂ) : ℂ := (a/n) * centerA (n*k) z
def innerB (n k a z : ℂ) : ℂ := (a/n) * centerB (n*k) z
def innerC (n k a z : ℂ) : ℂ := (a/n) * centerC (n*k) k z
def innerP (n k a z : ℂ) : ℂ := -(a/n) * (n*k)^2 * profile ((n*k)*z)
def outerA (k b z : ℂ) : ℂ := b*k*xiD 1 (k*z)/z
def outerB (k b z : ℂ) : ℂ := b*(2*xi 1 (k*z)/z^4-k*xiD 1 (k*z)/z^3)
def outerC (k b z : ℂ) : ℂ := b*I*k*xi 1 (k*z)/z^2
def outerP (n k a b z : ℂ) : ℂ :=
  -b*xi 1 (k*z)/z^2 + innerP n k a 1 + b*xi 1 k
def innerQ (n k a z : ℂ) : ℂ := innerA n k a z - innerP n k a z
def outerQ (n k a b z : ℂ) : ℂ := outerA k b z - outerP n k a b z

theorem innerA_differentiable (n k a : ℂ) : Differentiable ℂ (innerA n k a) :=
  (centerA_differentiable (n*k)).const_mul _

theorem innerB_differentiable (n k a : ℂ) : Differentiable ℂ (innerB n k a) :=
  (centerB_differentiable (n*k)).const_mul _

theorem innerC_differentiable (n k a : ℂ) : Differentiable ℂ (innerC n k a) :=
  (centerC_differentiable (n*k) k).const_mul _

theorem innerP_differentiable (n k a : ℂ) : Differentiable ℂ (innerP n k a) :=
  (profile_differentiable.comp ((differentiable_const _).mul differentiable_id)).const_mul _

theorem innerQ_differentiable (n k a : ℂ) : Differentiable ℂ (innerQ n k a) :=
  (innerA_differentiable n k a).sub (innerP_differentiable n k a)

theorem outerA_differentiableAt (k b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerA k b) z := by
  exact (((xiD_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).differentiableAt.comp z
    (differentiableAt_id.const_mul k)).const_mul (b*k)).div differentiableAt_id hz

theorem outerC_differentiableAt (k b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerC k b) z := by
  exact (((xi_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).differentiableAt.comp z
    (differentiableAt_id.const_mul k)).const_mul (b*I*k)).div
    (differentiableAt_id.pow 2) (pow_ne_zero _ hz)

theorem outerP_differentiableAt (n k a b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerP n k a b) z := by
  exact ((((xi_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).differentiableAt.comp z
    (differentiableAt_id.const_mul k)).const_mul (-b)).div
    (differentiableAt_id.pow 2) (pow_ne_zero _ hz)).add_const _ |>.add_const _

theorem outerQ_differentiableAt (n k a b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerQ n k a b) z :=
  (outerA_differentiableAt k b z hk hz).sub (outerP_differentiableAt n k a b z hk hz)

theorem entire_real_profile (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ContinuousOn (fun r : ℝ => f (r : ℂ)) (Ici 0) ∧
    ContinuousOn (fun r : ℝ => deriv f (r : ℂ)) (Ici 0) ∧
    ∀ r : ℝ, HasDerivAt (fun s : ℝ => f (s : ℂ)) (deriv f (r : ℂ)) r := by
  refine ⟨(hf.continuous.comp Complex.continuous_ofReal).continuousOn, ?_, ?_⟩
  · exact ((hf.differentiableOn.deriv isOpen_univ).continuousOn.comp
      Complex.continuous_ofReal.continuousOn (fun _ _ => mem_univ _))
  · intro r
    exact (hf (r : ℂ)).hasDerivAt.comp_ofReal

theorem punctured_real_profile (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) :
    ContinuousOn (fun r : ℝ => f (r : ℂ)) (Ioi 0) ∧
    ContinuousOn (fun r : ℝ => deriv f (r : ℂ)) (Ioi 0) ∧
    ∀ r : ℝ, 0 < r → HasDerivAt (fun s : ℝ => f (s : ℂ)) (deriv f (r : ℂ)) r := by
  have hd : DifferentiableOn ℂ f {z | z ≠ 0} :=
    fun z hz => (hf z hz).differentiableWithinAt
  have hm (r : ℝ) (hr : r ∈ Ioi 0) : (r : ℂ) ∈ {z : ℂ | z ≠ 0} :=
    ofReal_ne_zero.mpr (ne_of_gt hr)
  refine ⟨hd.continuousOn.comp Complex.continuous_ofReal.continuousOn hm, ?_, ?_⟩
  · exact (hd.deriv isOpen_ne).continuousOn.comp Complex.continuous_ofReal.continuousOn hm
  · intro r hr
    exact (hf (r : ℂ) (ofReal_ne_zero.mpr (ne_of_gt hr))).hasDerivAt.comp_ofReal

theorem potential_match (n k a b : ℂ) :
    innerP n k a 1 = outerP n k a b 1 := by
  simp [outerP]

theorem innerP_hasDerivAt (n k a z : ℂ) :
    HasDerivAt (innerP n k a) (z * innerB n k a z) z := by
  have hh := ((profile_differentiable ((n*k)*z)).hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (n*k))).const_mul (-(a/n)*(n*k)^2)
  have he := profileSlope_identity ((n*k)*z)
  convert hh using 1
  unfold innerB centerB
  linear_combination -(a/n)*(n*k)^3*he

theorem outerP_hasDerivAt (n k a b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    HasDerivAt (outerP n k a b) (z * outerB k b z) z := by
  have hxi := (xi_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).comp z
    ((hasDerivAt_id z).const_mul k)
  have hh := ((hxi.const_mul (-b)).div ((hasDerivAt_id z).pow 2)
    (pow_ne_zero 2 hz)).add_const (innerP n k a 1) |>.add_const (b*xi 1 k)
  convert hh using 1
  unfold outerB
  field_simp [hz]
  ring

theorem potential_derivatives (n k a b : ℂ) (hk : k ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    deriv (innerP n k a) z = z * innerB n k a z ∧
      deriv (outerP n k a b) z = z * outerB k b z :=
  ⟨(innerP_hasDerivAt n k a z).deriv, (outerP_hasDerivAt n k a b z hk hz).deriv⟩

theorem innerA_one (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    innerA n k a 1 = k * (psiD 1 (n*k) * a) := by
  have he := centerA_eq (n*k) (mul_ne_zero hn hk) 1 (by norm_num)
  rw [Complex.ofReal_one] at he
  rw [innerA, he]
  simp only [electricA, scaledRadialD, Complex.ofReal_one, mul_one, div_one]
  field_simp [hn]
  ring

theorem innerC_one (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    innerC n k a 1 = I*k*(n*psi 1 (n*k)*a) := by
  have he := centerC_eq (n*k) k (mul_ne_zero hn hk) 1 (by norm_num)
  rw [Complex.ofReal_one] at he
  rw [innerC, he]
  simp only [magneticC, scaledRadial, Complex.ofReal_one, mul_one, one_pow, div_one]
  field_simp [hn, hk]
  ring

theorem profiles_match (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : OQ14.ModalMatching.matching 1 n k (a,b) = 0) :
    innerA n k a 1 = outerA k b 1 ∧
    innerC n k a 1 = outerC k b 1 ∧
    innerQ n k a 1 = outerQ n k a b 1 := by
  have hH := congrArg Prod.fst hm
  have hE := congrArg Prod.snd hm
  change n*psi 1 (n*k)*a-xi 1 k*b = 0 at hH
  change psiD 1 (n*k)*a-xiD 1 k*b = 0 at hE
  have hA : innerA n k a 1 = outerA k b 1 := by
    rw [innerA_one n k a hn hk, sub_eq_zero.mp hE]
    simp only [outerA, mul_one, div_one]
    ring
  have hC : innerC n k a 1 = outerC k b 1 := by
    rw [innerC_one n k a hn hk, sub_eq_zero.mp hH]
    simp only [outerC, mul_one, one_pow, div_one]
    ring
  exact ⟨hA,hC,by rw [innerQ, outerQ, hA, potential_match]⟩

theorem potential_profile_hypotheses (n k a b : ℂ) (hk : k ≠ 0) :
    ContinuousOn (fun r : ℝ => innerP n k a r) (Ici 0) ∧
    ContinuousOn (fun r : ℝ => outerP n k a b r) (Ioi 0) ∧
    ContinuousOn (fun r : ℝ => deriv (innerP n k a) r) (Ici 0) ∧
    ContinuousOn (fun r : ℝ => deriv (outerP n k a b) r) (Ioi 0) ∧
    (∀ r : ℝ, 0 < r → HasDerivAt (fun s : ℝ => innerP n k a s)
      (deriv (innerP n k a) r) r) ∧
    (∀ r : ℝ, 0 < r → HasDerivAt (fun s : ℝ => outerP n k a b s)
      (deriv (outerP n k a b) r) r) := by
  have hi := entire_real_profile _ (innerP_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerP_differentiableAt n k a b z hk hz)
  exact ⟨hi.1,ho.1,hi.2.1,ho.2.1,fun r _ => hi.2.2 r,ho.2.2⟩

def potential (n k a b : ℂ) (x : Space) : ℂ :=
  radial (fun r => innerP n k a r) (fun r => outerP n k a b r) x * (x 2 : ℂ)

def potentialGradient (n k a b : ℂ) : Field := fun x i =>
  radialCoordinateD (fun r => innerP n k a r) (fun r => outerP n k a b r)
    (fun r => deriv (innerP n k a) r) (fun r => deriv (outerP n k a b) r) i 2 x

theorem potential_continuous (n k a b : ℂ) (hk : k ≠ 0) :
    Continuous (potential n k a b) := by
  have h := potential_profile_hypotheses n k a b hk
  exact (radial_continuous _ _ h.1 h.2.1 (potential_match n k a b)).mul (coordinate 2).continuous

theorem potential_actual_partial (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    dcoord (potential n k a b) x i = potentialGradient n k a b x i := by
  have h := potential_profile_hypotheses n k a b hk
  exact radial_coordinate_partial _ _ _ _ h.2.2.2.2.1 h.2.2.2.2.2 x hx0 hx1 i 2

theorem potentialGradient_locallyIntegrable (n k a b : ℂ) (hk : k ≠ 0) (i : Fin 3) :
    LocallyIntegrable (fun x => potentialGradient n k a b x i) := by
  have h := potential_profile_hypotheses n k a b hk
  exact radialCoordinateD_locallyIntegrable _ _ _ _ h.1 h.2.1 (potential_match n k a b)
    h.2.2.1 h.2.2.2.1 i 2

theorem potentialGradient_weak_curl_zero (n k a b : ℂ) (hk : k ≠ 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (potentialGradient n k a b) φ = 0 := by
  have h := potential_profile_hypotheses n k a b hk
  exact radialCoordinate_gradient_curl_zero _ _ _ _ h.1 h.2.1 (potential_match n k a b)
    h.2.2.2.2.1 h.2.2.2.2.2 h.2.2.1 h.2.2.2.1 2 φ hφ hc

def electric (n k a b : ℂ) : Field := fun x =>
  if ‖x‖ ≤ 1 then entireInnerE n k a x else outerE k b x

def magnetic (n k a b : ℂ) : Field := fun x =>
  if ‖x‖ ≤ 1 then entireInnerH n k a x else outerH k b x

def axial (n k a b : ℂ) : Field := fun x =>
  ![0,0,radial (fun r => innerQ n k a r) (fun r => outerQ n k a b r) x]

theorem electric_profiles (n k a b : ℂ) (x : Space) :
    electric n k a b x =
      ![radial (fun r => innerB n k a r) (fun r => outerB k b r) x * (x 2 : ℂ) * (x 0 : ℂ),
        radial (fun r => innerB n k a r) (fun r => outerB k b r) x * (x 2 : ℂ) * (x 1 : ℂ),
        radial (fun r => innerA n k a r) (fun r => outerA k b r) x +
          radial (fun r => innerB n k a r) (fun r => outerB k b r) x * (x 2 : ℂ) * (x 2 : ℂ)] := by
  unfold electric radial
  split_ifs <;> ext j <;> fin_cases j <;>
    simp [entireInnerE, centerE, innerA, innerB, outerE, outgoingE, dipoleE, axisField,
      outerA, outerB, electricA, electricB, scaledRadial, scaledRadialD, div_eq_mul_inv] <;> ring

theorem magnetic_profiles (n k a b : ℂ) (hk : k ≠ 0) (x : Space) :
    magnetic n k a b x =
      ![radial (fun r => innerC n k a r) (fun r => outerC k b r) x * (x 1 : ℂ),
        -radial (fun r => innerC n k a r) (fun r => outerC k b r) x * (x 0 : ℂ),0] := by
  have hkk : I*k^2/k = I*k := by field_simp [hk]; ring
  unfold magnetic radial
  split_ifs <;> ext j <;> fin_cases j <;>
    simp [entireInnerH, centerH, innerC, outerH, outgoingH, dipoleH, swirlField,
      outerC, magneticC, scaledRadial, hkk]
  all_goals (simp only [div_eq_mul_inv]; ring)

theorem potentialGradient_formula (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    potentialGradient n k a b x i =
      radial (fun r => innerP n k a r) (fun r => outerP n k a b r) x *
        (if i = 2 then 1 else 0) +
      radial (fun r => innerB n k a r) (fun r => outerB k b r) x * (x 2 : ℂ) * (x i : ℂ) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  unfold potentialGradient radialCoordinateD radialD radial
  dsimp only
  rw [(innerP_hasDerivAt n k a (‖x‖ : ℂ)).deriv,
    (outerP_hasDerivAt n k a b (‖x‖ : ℂ) hk hr).deriv]
  split_ifs <;> push_cast <;> field_simp [hr] <;> ring

theorem electric_decomposition (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : x ≠ 0) :
    electric n k a b x = fun i => potentialGradient n k a b x i + axial n k a b x i := by
  rw [electric_profiles]
  have hq : radial (fun r => innerQ n k a r) (fun r => outerQ n k a b r) x =
      radial (fun r => innerA n k a r) (fun r => outerA k b r) x -
      radial (fun r => innerP n k a r) (fun r => outerP n k a b r) x := by
    unfold radial innerQ outerQ
    split_ifs <;> rfl
  ext i
  rw [potentialGradient_formula n k a b hk x hx]
  fin_cases i <;> simp [axial, hq]
  ring

theorem axial_continuous (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : OQ14.ModalMatching.matching 1 n k (a,b) = 0) (i : Fin 3) :
    Continuous (fun x => axial n k a b x i) := by
  have hi := entire_real_profile _ (innerQ_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerQ_differentiableAt n k a b z hk hz)
  have he := (profiles_match n k a b hn hk hm).2.2
  have hc := radial_continuous _ _ hi.1 ho.1 (by simpa using he)
  fin_cases i <;> simp only [axial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]
  · exact continuous_const
  · exact continuous_const
  · exact hc

theorem magnetic_continuous (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : OQ14.ModalMatching.matching 1 n k (a,b) = 0) (i : Fin 3) :
    Continuous (fun x => magnetic n k a b x i) := by
  have hi := entire_real_profile _ (innerC_differentiable n k a)
  have ho := punctured_real_profile _ (fun z hz => outerC_differentiableAt k b z hk hz)
  have he := (profiles_match n k a b hn hk hm).2.1
  have hc := radial_continuous _ _ hi.1 ho.1 (by simpa using he)
  have hform := funext (magnetic_profiles n k a b hk)
  rw [hform]
  fin_cases i
  · exact hc.mul (coordinate 1).continuous
  · exact hc.neg.mul (coordinate 0).continuous
  · exact continuous_const

theorem electric_eventually_inner (n k a b : ℂ) (x : Space) (hx : ‖x‖ < 1) :
    electric n k a b =ᶠ[𝓝 x] entireInnerE n k a := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
  exact if_pos hy.le

theorem electric_eventually_outer (n k a b : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    electric n k a b =ᶠ[𝓝 x] outerE k b := by
  filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
  exact if_neg (not_le.mpr hy)

theorem magnetic_eventually_inner (n k a b : ℂ) (x : Space) (hx : ‖x‖ < 1) :
    magnetic n k a b =ᶠ[𝓝 x] entireInnerH n k a := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
  exact if_pos hy.le

theorem magnetic_eventually_outer (n k a b : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    magnetic n k a b =ᶠ[𝓝 x] outerH k b := by
  filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
  exact if_neg (not_le.mpr hy)

def coefficient (n : ℂ) (x : Space) : ℂ := if ‖x‖ ≤ 1 then n^2 else 1

theorem assembled_classical_maxwell (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (x : Space) (hx : ‖x‖ ≠ 1) :
    ComplexMaxwellAt k (coefficient n x) (electric n k a b) (magnetic n k a b) x := by
  rcases hx.lt_or_lt with hx | hx
  · have hm := entireInner_maxwell n k a hn hk x
    have he := electric_eventually_inner n k a b x hx
    have hh := magnetic_eventually_inner n k a b x hx
    constructor
    · rw [curl_eventuallyEq _ _ x he, hm.1]
      simp only [magnetic, hx.le, if_true]
    · rw [curl_eventuallyEq _ _ x hh, hm.2]
      simp only [electric, coefficient, hx.le, if_true]
  · have hx0 : x ≠ 0 := by intro he; norm_num [he] at hx
    have hm := outer_maxwell k b hk x hx0
    have he := electric_eventually_outer n k a b x hx
    have hh := magnetic_eventually_outer n k a b x hx
    constructor
    · rw [curl_eventuallyEq _ _ x he, hm.1]
      simp only [magnetic, not_le.mpr hx, if_false]
    · rw [curl_eventuallyEq _ _ x hh, hm.2]
      simp only [electric, coefficient, not_le.mpr hx, if_false]

end OQ14.ModalProfiles

#print axioms OQ14.ModalProfiles.innerA_differentiable
#print axioms OQ14.ModalProfiles.innerB_differentiable
#print axioms OQ14.ModalProfiles.innerC_differentiable
#print axioms OQ14.ModalProfiles.innerP_differentiable
#print axioms OQ14.ModalProfiles.innerQ_differentiable
#print axioms OQ14.ModalProfiles.outerA_differentiableAt
#print axioms OQ14.ModalProfiles.outerC_differentiableAt
#print axioms OQ14.ModalProfiles.outerP_differentiableAt
#print axioms OQ14.ModalProfiles.outerQ_differentiableAt
#print axioms OQ14.ModalProfiles.entire_real_profile
#print axioms OQ14.ModalProfiles.punctured_real_profile
#print axioms OQ14.ModalProfiles.potential_match
#print axioms OQ14.ModalProfiles.innerP_hasDerivAt
#print axioms OQ14.ModalProfiles.outerP_hasDerivAt
#print axioms OQ14.ModalProfiles.potential_derivatives
#print axioms OQ14.ModalProfiles.innerA_one
#print axioms OQ14.ModalProfiles.innerC_one
#print axioms OQ14.ModalProfiles.profiles_match
#print axioms OQ14.ModalProfiles.potential_profile_hypotheses
#print axioms OQ14.ModalProfiles.potential_continuous
#print axioms OQ14.ModalProfiles.potential_actual_partial
#print axioms OQ14.ModalProfiles.potentialGradient_locallyIntegrable
#print axioms OQ14.ModalProfiles.potentialGradient_weak_curl_zero
#print axioms OQ14.ModalProfiles.electric_profiles
#print axioms OQ14.ModalProfiles.magnetic_profiles
#print axioms OQ14.ModalProfiles.potentialGradient_formula
#print axioms OQ14.ModalProfiles.electric_decomposition
#print axioms OQ14.ModalProfiles.axial_continuous
#print axioms OQ14.ModalProfiles.magnetic_continuous
#print axioms OQ14.ModalProfiles.electric_eventually_inner
#print axioms OQ14.ModalProfiles.electric_eventually_outer
#print axioms OQ14.ModalProfiles.magnetic_eventually_inner
#print axioms OQ14.ModalProfiles.magnetic_eventually_outer
#print axioms OQ14.ModalProfiles.assembled_classical_maxwell
