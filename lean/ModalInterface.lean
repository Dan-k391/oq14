import ModalDipole

/-!
# Actual tangential interface matching for the dipole fields

The tangential trace here is the actual cross product with the radius
vector. Equality is equivalent to equality with the unit normal when the
radius is positive. No Maxwell trace/matching equivalence is a premise.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.ModalInterface

open Complex Matrix OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ModalDipole

def tangent (x : Space) (v : Vector) : Vector := crossProduct (fun j => (x j : ℂ)) v

theorem tangent_smul (x : Space) (c : ℂ) (v : Vector) :
    tangent x (c • v) = c • tangent x v := (crossProduct (fun j => (x j : ℂ))).map_smul c v

theorem tangent_axis (A B : ℝ → ℂ) (x : Space) :
    tangent x (axisField A B x) =
      ![A ‖x‖ * (x 1 : ℂ), -A ‖x‖ * (x 0 : ℂ), 0] := by
  ext j
  fin_cases j <;> simp [tangent, axisField, cross_apply] <;> ring

theorem tangent_swirl (C : ℝ → ℂ) (x : Space) :
    tangent x (swirlField C x) =
      ![C ‖x‖ * (x 2 : ℂ) * (x 0 : ℂ), C ‖x‖ * (x 2 : ℂ) * (x 1 : ℂ),
        -C ‖x‖ * ((x 0 : ℂ)^2 + (x 1 : ℂ)^2)] := by
  ext j
  fin_cases j <;> simp [tangent, swirlField, cross_apply] <;> ring

def innerE (n k a : ℂ) : Field := fun x => (a / n) • regularE (n * k) x
def innerH (n k a : ℂ) : Field := fun x => (a / n) • regularH (n * k) k x
def outerE (k b : ℂ) : Field := fun x => b • outgoingE k x
def outerH (k b : ℂ) : Field := fun x => b • outgoingH k k x

def electricTraceCoefficient (n k a : ℂ) (r : ℝ) : ℂ :=
  a * k * psiD 1 (n * (k * r)) / (r : ℂ)
def outgoingElectricCoefficient (k b : ℂ) (r : ℝ) : ℂ :=
  b * k * xiD 1 (k * r) / (r : ℂ)
def magneticTraceCoefficient (n k a : ℂ) (r : ℝ) : ℂ :=
  I * k * (n * psi 1 (n * (k * r)) * a) / (r : ℂ)^2
def outgoingMagneticCoefficient (k b : ℂ) (r : ℝ) : ℂ :=
  I * k * (xi 1 (k * r) * b) / (r : ℂ)^2

theorem innerE_trace (n k a : ℂ) (hn : n ≠ 0) (x : Space) :
    tangent x (innerE n k a x) =
      ![electricTraceCoefficient n k a ‖x‖ * (x 1 : ℂ),
        -electricTraceCoefficient n k a ‖x‖ * (x 0 : ℂ), 0] := by
  rw [innerE, tangent_smul]
  change (a / n) • tangent x (axisField _ _ x) = _
  rw [tangent_axis]
  ext j
  fin_cases j <;> simp [electricA, scaledRadialD, electricTraceCoefficient, mul_assoc]
  all_goals simp only [div_eq_mul_inv, ← inv_pow]
  all_goals generalize (‖x‖ : ℂ)⁻¹ = r
  all_goals field_simp [hn]
  all_goals ring

theorem outerE_trace (k b : ℂ) (x : Space) :
    tangent x (outerE k b x) =
      ![outgoingElectricCoefficient k b ‖x‖ * (x 1 : ℂ),
        -outgoingElectricCoefficient k b ‖x‖ * (x 0 : ℂ), 0] := by
  rw [outerE, tangent_smul]
  change b • tangent x (axisField _ _ x) = _
  rw [tangent_axis]
  ext j
  fin_cases j <;> simp [electricA, scaledRadialD, outgoingElectricCoefficient] <;> ring

theorem innerH_trace (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (x : Space) :
    tangent x (innerH n k a x) =
      ![magneticTraceCoefficient n k a ‖x‖ * (x 2 : ℂ) * (x 0 : ℂ),
        magneticTraceCoefficient n k a ‖x‖ * (x 2 : ℂ) * (x 1 : ℂ),
        -magneticTraceCoefficient n k a ‖x‖ * ((x 0 : ℂ)^2 + (x 1 : ℂ)^2)] := by
  rw [innerH, tangent_smul]
  change (a / n) • tangent x (swirlField _ x) = _
  rw [tangent_swirl]
  ext j
  fin_cases j <;> simp [magneticC, scaledRadial, magneticTraceCoefficient, mul_assoc]
  all_goals simp only [div_eq_mul_inv, ← inv_pow]
  all_goals generalize (‖x‖ : ℂ)⁻¹ = r
  all_goals field_simp [hn, hk]
  all_goals ring

theorem outerH_trace (k b : ℂ) (hk : k ≠ 0) (x : Space) :
    tangent x (outerH k b x) =
      ![outgoingMagneticCoefficient k b ‖x‖ * (x 2 : ℂ) * (x 0 : ℂ),
        outgoingMagneticCoefficient k b ‖x‖ * (x 2 : ℂ) * (x 1 : ℂ),
        -outgoingMagneticCoefficient k b ‖x‖ * ((x 0 : ℂ)^2 + (x 1 : ℂ)^2)] := by
  rw [outerH, tangent_smul]
  change b • tangent x (swirlField _ x) = _
  rw [tangent_swirl]
  ext j
  fin_cases j <;> simp [magneticC, scaledRadial, outgoingMagneticCoefficient]
  all_goals simp only [div_eq_mul_inv, ← inv_pow]
  all_goals generalize (‖x‖ : ℂ)⁻¹ = r
  all_goals field_simp [hk]
  all_goals ring

def SphereMatches (n k : ℂ) (R : ℝ) (v : Amplitudes) : Prop :=
  ∀ x : Space, ‖x‖ = R →
    tangent x (innerE n k v.1 x) = tangent x (outerE k v.2 x) ∧
      tangent x (innerH n k v.1 x) = tangent x (outerH k v.2 x)

theorem matching_implies_sphere_matches (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (R : ℝ) (v : Amplitudes) (hm : matching 1 n (k * R) v = 0) :
    SphereMatches n k R v := by
  have hmH := congrArg Prod.fst hm
  have hmE := congrArg Prod.snd hm
  dsimp only [matching, Prod.fst_zero, Prod.snd_zero] at hmH hmE
  have he : electricTraceCoefficient n k v.1 R = outgoingElectricCoefficient k v.2 R := by
    unfold electricTraceCoefficient outgoingElectricCoefficient
    have heq := sub_eq_zero.mp hmE
    rw [show v.1 * k * psiD 1 (n * (k * R)) = k * (psiD 1 (n * (k * R)) * v.1) by ring,
      heq]
    ring
  have hh : magneticTraceCoefficient n k v.1 R = outgoingMagneticCoefficient k v.2 R := by
    unfold magneticTraceCoefficient outgoingMagneticCoefficient
    rw [sub_eq_zero.mp hmH]
  intro x hx
  constructor
  · rw [innerE_trace n k v.1 hn, outerE_trace, hx, he]
  · rw [innerH_trace n k v.1 hn hk, outerH_trace k v.2 hk, hx, hh]

theorem sphere_matches_implies_matching (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (R : ℝ) (hR : 0 < R) (v : Amplitudes) (hm : SphereMatches n k R v) :
    matching 1 n (k * R) v = 0 := by
  let x : Space := EuclideanSpace.single 0 R
  have hx : ‖x‖ = R := by simp [x, Real.norm_eq_abs, abs_of_pos hR]
  have hrc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  obtain ⟨he, hh⟩ := hm x hx
  rw [innerE_trace n k v.1 hn, outerE_trace k v.2, hx] at he
  rw [innerH_trace n k v.1 hn hk, outerH_trace k v.2 hk, hx] at hh
  have he1 := congrArg (fun w : Vector => w 1) he
  have hh2 := congrArg (fun w : Vector => w 2) hh
  simp [x, EuclideanSpace.single_apply] at he1 hh2
  unfold electricTraceCoefficient outgoingElectricCoefficient at he1
  unfold magneticTraceCoefficient outgoingMagneticCoefficient at hh2
  field_simp [hrc] at he1 hh2
  have he1 := he1.resolve_right hR.ne'
  have hh2 := hh2.resolve_right hR.ne'
  have he0 : k * (psiD 1 (n * (k * R)) * v.1 - xiD 1 (k * R) * v.2) = 0 := by
    linear_combination he1
  have hh0 : (I * k) * (n * psi 1 (n * (k * R)) * v.1 - xi 1 (k * R) * v.2) = 0 := by
    linear_combination (I * k) * hh2
  apply Prod.ext
  · exact (mul_eq_zero.mp hh0).resolve_left (mul_ne_zero I_ne_zero hk)
  · exact (mul_eq_zero.mp he0).resolve_left hk

/-- The actual all-sphere tangential transmission conditions are exactly
the previously constructed two-amplitude TM matching equations. -/
theorem sphere_matching_iff (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (R : ℝ) (hR : 0 < R) (v : Amplitudes) :
    SphereMatches n k R v ↔ matching 1 n (k * R) v = 0 :=
  ⟨sphere_matches_implies_matching n k hn hk R hR v,
    matching_implies_sphere_matches n k hn hk R v⟩

/-- A determinant zero is equivalent to a nonzero amplitude pair whose
actual dipole electric and magnetic fields satisfy the interface traces. -/
theorem determinant_iff_nontrivial_interface (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    tmDet 1 n (k * R) = 0 ↔ ∃ v : Amplitudes, v ≠ 0 ∧ SphereMatches n k R v := by
  have hkr : k * (R : ℂ) ≠ 0 := mul_ne_zero hk (ofReal_ne_zero.mpr hR.ne')
  rw [matching_kernel_iff 1 n (k * R) hkr]
  constructor
  · rintro ⟨v, hv, hm⟩
    exact ⟨v, hv, (sphere_matching_iff n k hn hk R hR v).mpr hm⟩
  · rintro ⟨v, hv, hm⟩
    exact ⟨v, hv, (sphere_matching_iff n k hn hk R hR v).mp hm⟩

theorem regular_outgoing_wronskian (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    psi l z * xiD l z - xi l z * psiD l z = I := by
  have hw := OQ14.ModalWronskian.hankel_wronskian l z hz
  unfold psi psiD
  linear_combination -(1 / 2 : ℂ) * hw

theorem regular_state_nonzero (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    psi l z ≠ 0 ∨ psiD l z ≠ 0 := by
  classical
  by_cases h : psi l z = 0
  · right
    intro hd
    have hw := regular_outgoing_wronskian l z hz
    rw [h, hd] at hw
    norm_num at hw
    exact I_ne_zero hw.symm
  · exact Or.inl h

theorem matching_nonzero_amplitudes (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (v : Amplitudes) (hv : v ≠ 0) (hm : matching l n z v = 0) : v.1 ≠ 0 ∧ v.2 ≠ 0 := by
  have h0 := congrArg Prod.fst hm
  have h1 := congrArg Prod.snd hm
  dsimp only [matching, Prod.fst_zero, Prod.snd_zero] at h0 h1
  constructor
  · intro ha
    have hb : v.2 ≠ 0 := by
      intro hb
      exact hv (Prod.ext ha hb)
    rw [ha, mul_zero, zero_sub] at h0 h1
    have hx := (mul_eq_zero.mp (neg_eq_zero.mp h0)).resolve_right hb
    have hxd := (mul_eq_zero.mp (neg_eq_zero.mp h1)).resolve_right hb
    exact (outgoing_state_nonzero l z hz).elim (fun h => h hx) (fun h => h hxd)
  · intro hb
    have ha : v.1 ≠ 0 := by
      intro ha
      exact hv (Prod.ext ha hb)
    rw [hb, mul_zero, sub_zero] at h0 h1
    have hp := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right ha)).resolve_left hn
    have hpd := (mul_eq_zero.mp h1).resolve_right ha
    exact (regular_state_nonzero l (n * z) (mul_ne_zero hn hz)).elim
      (fun h => h hp) (fun h => h hpd)

theorem outer_traces_not_both_zero (k b : ℂ) (hk : k ≠ 0) (hb : b ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ x : Space, ‖x‖ = R ∧
      (tangent x (outerE k b x) ≠ 0 ∨ tangent x (outerH k b x) ≠ 0) := by
  classical
  let x : Space := EuclideanSpace.single 0 R
  have hx : ‖x‖ = R := by simp [x, Real.norm_eq_abs, abs_of_pos hR]
  have hrc : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  refine ⟨x, hx, ?_⟩
  by_contra h
  push_neg at h
  have he := congrArg (fun w : Vector => w 1) h.1
  have hh := congrArg (fun w : Vector => w 2) h.2
  rw [outerE_trace k b x, hx] at he
  rw [outerH_trace k b hk x, hx] at hh
  simp [x, EuclideanSpace.single_apply, outgoingElectricCoefficient,
    outgoingMagneticCoefficient, hk, hb, hR.ne'] at he hh
  exact (outgoing_state_nonzero 1 (k * R) (mul_ne_zero hk hrc)).elim
    (fun h => h hh) (fun h => h he)

/-- Nonzero matching amplitudes yield actual nonzero field traces, so
the determinant/interface equivalence cannot be satisfied by zero fields. -/
theorem nontrivial_interface_has_nonzero_trace (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (R : ℝ) (hR : 0 < R) (v : Amplitudes) (hv : v ≠ 0) (hm : SphereMatches n k R v) :
    ∃ x : Space, ‖x‖ = R ∧
      (tangent x (outerE k v.2 x) ≠ 0 ∨ tangent x (outerH k v.2 x) ≠ 0) := by
  have hkr := mul_ne_zero hk (ofReal_ne_zero.mpr hR.ne')
  have hamp := matching_nonzero_amplitudes 1 n (k * R) hn hkr v hv
    ((sphere_matching_iff n k hn hk R hR v).mp hm)
  exact outer_traces_not_both_zero k v.2 hk hamp.2 R hR

theorem dipoleE_differentiableAt (u uD : ℝ → ℂ) (w : ℂ) (x : Space) (hx : x ≠ 0)
    (hu : HasDerivAt u (uD ‖x‖) ‖x‖) (hv : HasDerivAt uD w ‖x‖) :
    ∀ j, DifferentiableAt ℝ (fun y => dipoleE u uD y j) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hnorm := (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have ha := ((electricA_hasDerivAt uD w ‖x‖ hr hv).hasFDerivAt.comp x hnorm).differentiableAt
  have hb := ((electricB_hasDerivAt u uD w ‖x‖ hr hu hv).hasFDerivAt.comp x hnorm).differentiableAt
  intro j
  fin_cases j
  · exact (hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 0)
  · exact (hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 1)
  · exact ha.add ((hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 2))

theorem dipoleH_differentiableAt (κ k : ℂ) (u uD : ℝ → ℂ) (x : Space) (hx : x ≠ 0)
    (hu : HasDerivAt u (uD ‖x‖) ‖x‖) :
    ∀ j, DifferentiableAt ℝ (fun y => dipoleH κ k u y j) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hnorm := (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hc := ((magneticC_hasDerivAt κ k u uD ‖x‖ hr hu).hasFDerivAt.comp x hnorm).differentiableAt
  intro j
  fin_cases j
  · exact hc.mul (coordinate_differentiableAt x 1)
  · exact hc.neg.mul (coordinate_differentiableAt x 0)
  · exact differentiableAt_const _

theorem complexMaxwell_scale (k ε c : ℂ) (E H : Field) (x : Space)
    (hE : ∀ j, DifferentiableAt ℝ (fun y => E y j) x)
    (hH : ∀ j, DifferentiableAt ℝ (fun y => H y j) x)
    (hm : ComplexMaxwellAt k ε E H x) :
    ComplexMaxwellAt k ε (fun y => c • E y) (fun y => c • H y) x := by
  constructor
  · change curl (fun y j => c * E y j) x = _
    rw [curl_const_mul E x c hE, hm.1]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · change curl (fun y j => c * H y j) x = _
    rw [curl_const_mul H x c hH, hm.2]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem scaled_radial_dipole_maxwell (u uD : ℝ → ℂ) (w κ k ε c : ℂ)
    (x : Space) (hx : x ≠ 0) (hk : k ≠ 0) (hκ : κ^2 = k^2 * ε)
    (hu : HasDerivAt u (uD ‖x‖) ‖x‖) (hv : HasDerivAt uD w ‖x‖)
    (ho : w = (2 / (‖x‖ : ℂ)^2 - κ^2) * u ‖x‖) :
    ComplexMaxwellAt k ε (fun y => c • dipoleE u uD y) (fun y => c • dipoleH κ k u y) x :=
  complexMaxwell_scale k ε c _ _ x (dipoleE_differentiableAt u uD w x hx hu hv)
    (dipoleH_differentiableAt κ k u uD x hx hu)
    (radial_dipole_maxwell u uD w κ k ε x hx hk hκ hu hv ho)

theorem inner_maxwell (n k a : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k (n^2) (innerE n k a) (innerH n k a) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hnk := mul_ne_zero hn hk
  have hz := mul_ne_zero hnk hrc
  have hu := scaledRadial_hasDerivAt (psi 1) (psiD 1) (n * k) ‖x‖ (psi_hasDerivAt 1 _ hz)
  have hsecond : HasDerivAt (psiD 1)
      ((2 / ((n * k) * ‖x‖)^2 - 1) * psi 1 ((n * k) * ‖x‖)) ((n * k) * ‖x‖) := by
    simpa only [Nat.cast_one, one_add_one_eq_two, one_mul] using
      OQ14.ModalMatching.psiD_hasDerivAt 1 ((n * k) * ‖x‖) hz
  have hv := scaledRadialD_hasDerivAt (psi 1) (psiD 1) (n * k) hnk ‖x‖ hr hsecond
  exact scaled_radial_dipole_maxwell _ _ _ (n * k) k (n^2) (a / n) x hx hk (by ring) hu hv rfl

theorem outer_maxwell (k b : ℂ) (hk : k ≠ 0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k 1 (outerE k b) (outerH k b) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hz := mul_ne_zero hk hrc
  have hu := scaledRadial_hasDerivAt (xi 1) (xiD 1) k ‖x‖ (xi_hasDerivAt 1 _ hz)
  have hsecond : HasDerivAt (xiD 1)
      ((2 / (k * ‖x‖)^2 - 1) * xi 1 (k * ‖x‖)) (k * ‖x‖) := by
    simpa only [Nat.cast_one, one_add_one_eq_two, one_mul] using
      OQ14.ModalWronskian.xiD_hasDerivAt 1 (k * ‖x‖) hz
  have hv := scaledRadialD_hasDerivAt (xi 1) (xiD 1) k hk ‖x‖ hr hsecond
  exact scaled_radial_dipole_maxwell _ _ _ k k 1 b x hx hk (by ring) hu hv rfl

/-- Actual dipole field pairs with matching spherical traces exist at
complex frequencies of arbitrarily large frequency-to-decay ratio.
The interior Maxwell equation here is still restricted away from zero. -/
theorem exists_high_quality_transmission_fields (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k a b : ℂ, k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ L < k.re ∧ k.im < 0 ∧
      Q < k.re / (-2 * k.im) ∧ SphereMatches (n : ℂ) k 1 (a, b) ∧
      (∀ x : Space, x ≠ 0 → ComplexMaxwellAt k ((n : ℂ)^2)
        (innerE (n : ℂ) k a) (innerH (n : ℂ) k a) x) ∧
      (∀ x : Space, x ≠ 0 → ComplexMaxwellAt k 1 (outerE k b) (outerH k b) x) ∧
      ∃ x : Space, ‖x‖ = 1 ∧
        (tangent x (outerE k b x) ≠ 0 ∨ tangent x (outerH k b x) ≠ 0) := by
  obtain ⟨k, hk, hd, -, hL, hi, hratio⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros 1 n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hd' : tmDet 1 (n : ℂ) (k * (1 : ℝ)) = 0 := by simpa using hd
  obtain ⟨v, hv, hmatch⟩ := (determinant_iff_nontrivial_interface
    (n : ℂ) k hn0 hk 1 (by norm_num)).mp hd'
  have hma := (sphere_matching_iff (n : ℂ) k hn0 hk 1 (by norm_num) v).mp hmatch
  have hkr : k * ((1 : ℝ) : ℂ) ≠ 0 := by simpa using hk
  have hamp := matching_nonzero_amplitudes 1 (n : ℂ) _ hn0 hkr v hv hma
  refine ⟨k, v.1, v.2, hk, hamp.1, hamp.2, hL, hi, hratio, hmatch, ?_, ?_, ?_⟩
  · exact fun x hx => inner_maxwell (n : ℂ) k v.1 hn0 hk x hx
  · exact fun x hx => outer_maxwell k v.2 hk x hx
  · exact outer_traces_not_both_zero k v.2 hk hamp.2 1 (by norm_num)

end OQ14.ModalInterface

#print axioms OQ14.ModalInterface.tangent_smul
#print axioms OQ14.ModalInterface.tangent_axis
#print axioms OQ14.ModalInterface.tangent_swirl
#print axioms OQ14.ModalInterface.innerE_trace
#print axioms OQ14.ModalInterface.outerE_trace
#print axioms OQ14.ModalInterface.innerH_trace
#print axioms OQ14.ModalInterface.outerH_trace
#print axioms OQ14.ModalInterface.matching_implies_sphere_matches
#print axioms OQ14.ModalInterface.sphere_matches_implies_matching
#print axioms OQ14.ModalInterface.sphere_matching_iff
#print axioms OQ14.ModalInterface.determinant_iff_nontrivial_interface
#print axioms OQ14.ModalInterface.regular_outgoing_wronskian
#print axioms OQ14.ModalInterface.regular_state_nonzero
#print axioms OQ14.ModalInterface.matching_nonzero_amplitudes
#print axioms OQ14.ModalInterface.outer_traces_not_both_zero
#print axioms OQ14.ModalInterface.nontrivial_interface_has_nonzero_trace
#print axioms OQ14.ModalInterface.dipoleE_differentiableAt
#print axioms OQ14.ModalInterface.dipoleH_differentiableAt
#print axioms OQ14.ModalInterface.complexMaxwell_scale
#print axioms OQ14.ModalInterface.scaled_radial_dipole_maxwell
#print axioms OQ14.ModalInterface.inner_maxwell
#print axioms OQ14.ModalInterface.outer_maxwell
#print axioms OQ14.ModalInterface.exists_high_quality_transmission_fields
