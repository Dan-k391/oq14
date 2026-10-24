import StaticPlaneKernel

/-! Static dipole kernel at a plane point: explicit tangential-normal Hessian entries, the radial profile weight,
its half-disk integrals and their scaling limit as the dipole height tends to zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEDipoleProfile
open MeasureTheory Metric Set Filter
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane

/-- Real inner product on the plane. -/
def ip (n ξ : Plane) : ℝ := @inner ℝ _ _ n ξ

theorem ip_smul (n ξ : Plane) (a : ℝ) : ip n (a • ξ)=a*ip n ξ := real_inner_smul_right n ξ a

theorem ip_neg (n ξ : Plane) : ip n (-ξ)=-ip n ξ := inner_neg_right n ξ

theorem ip_continuous (n : Plane) : Continuous (ip n) := continuous_const.inner continuous_id

theorem abs_ip_le (n ξ : Plane) : |ip n ξ|≤‖n‖*‖ξ‖ := abs_real_inner_le_norm n ξ

/-- The point of `ℝ³` above the horizontal position `c` at height `t`. -/
def abovePoint (c : Plane) (t : ℝ) : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![c 0, c 1, t]

/-- Distance from the observation point `planePoint q` to the dipole centre above `c`, in terms of `ξ = q - c`. -/
def rad (t : ℝ) (ξ : Plane) : ℝ := Real.sqrt (‖ξ‖^2+t^2)

/-- The radial weight of the tangential-normal static dipole field. -/
def prof (t : ℝ) (ξ : Plane) : ℝ := 3*t/(4*Real.pi*(rad t ξ)^5)

theorem norm_sq_plane (ξ : Plane) : ‖ξ‖^2=(ξ 0)^2+(ξ 1)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem norm_sq_space (z : Space) : ‖z‖^2=(z 0)^2+(z 1)^2+(z 2)^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem norm_diff (q c : Plane) (t : ℝ) :
    ‖MaxwellPlaneTail.planePoint q-abovePoint c t‖=rad t (q-c) := by
  have h : ‖MaxwellPlaneTail.planePoint q-abovePoint c t‖^2=‖q-c‖^2+t^2 := by
    rw [norm_sq_space, norm_sq_plane]
    simp [MaxwellPlaneTail.planePoint, abovePoint]
  unfold rad
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem rad_pos (t : ℝ) (ht : 0<t) (ξ : Plane) : 0<rad t ξ := by
  unfold rad
  exact Real.sqrt_pos.mpr (by positivity)

theorem le_rad_left (t : ℝ) (ξ : Plane) : ‖ξ‖≤rad t ξ := by
  unfold rad
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])

theorem le_rad_right (t : ℝ) (ξ : Plane) : t≤rad t ξ := by
  unfold rad
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖ξ‖])

theorem rad_sq (t : ℝ) (ξ : Plane) : (rad t ξ)^2=‖ξ‖^2+t^2 := by
  unfold rad
  exact Real.sq_sqrt (by positivity)

theorem prof_nonneg (t : ℝ) (ht : 0<t) (ξ : Plane) : 0≤prof t ξ := by
  have := rad_pos t ht ξ
  unfold prof
  positivity

theorem prof_neg (t : ℝ) (ξ : Plane) : prof t (-ξ)=prof t ξ := by
  simp [prof, rad]

theorem phiHessian_static_off (z : Space) (hz : z≠0) (i j : Fin 3) (hij : i≠j) :
    GreenKernel.phiHessian 0 z i j=((3*z i*z j/(4*Real.pi*‖z‖^5) : ℝ) : ℂ) := by
  have hr : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  have hrC : (‖z‖ : ℂ)≠0 := by exact_mod_cast hr
  have hpi : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  unfold GreenKernel.phiHessian GreenKernel.radialD GreenKernel.radialDD
  simp only [hij, if_false, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, zero_div,
    sub_zero, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add, zero_sub]
  push_cast
  generalize (‖z‖ : ℂ)=r at hrC ⊢
  generalize (Real.pi : ℂ)=P at hpi ⊢
  have h5 : r^5≠0 := pow_ne_zero 5 hrC
  rw [div_eq_div_iff (mul_ne_zero (by norm_num) hpi) (mul_ne_zero (mul_ne_zero (by norm_num) hpi) h5)]
  field_simp
  ring

theorem diff_tangent (q c : Plane) (t : ℝ) (i : Fin 2) :
    (MaxwellPlaneTail.planePoint q-abovePoint c t) (Fin.castSucc i)=(q-c) i := by
  fin_cases i <;> simp [MaxwellPlaneTail.planePoint, abovePoint]

theorem diff_normal (q c : Plane) (t : ℝ) :
    (MaxwellPlaneTail.planePoint q-abovePoint c t) 2=-t := by
  simp [MaxwellPlaneTail.planePoint, abovePoint]

/-- The tangential-normal Hessian entries of the static kernel at a plane point seen from a dipole at height
`t>0` above `c`: `∂_i ∂_z Φ = - prof t ξ * ξ_i` with `ξ = q - c`. -/
theorem hess_tangent_normal (q c : Plane) (t : ℝ) (ht : 0<t) (i : Fin 2) :
    GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-abovePoint c t) (Fin.castSucc i) 2=
      ((-(prof t (q-c)*(q-c) i) : ℝ) : ℂ) := by
  have hz : MaxwellPlaneTail.planePoint q-abovePoint c t≠0 := by
    intro h
    have := diff_normal q c t
    rw [h] at this
    simp at this
    linarith
  rw [phiHessian_static_off _ hz (Fin.castSucc i) 2 (by fin_cases i <;> simp [Fin.ext_iff]),
    diff_tangent, diff_normal, norm_diff]
  unfold prof
  congr 1
  ring

/-- Open half plane `{ξ | 0 < ip n ξ}`. -/
def U (n : Plane) : Set Plane := {ξ | 0 < ip n ξ}

theorem U_measurable (n : Plane) : MeasurableSet (U n) :=
  measurableSet_lt measurable_const (ip_continuous n).measurable

/-- The tangential flux profile `ip n ξ * prof t ξ`. -/
def psi (n : Plane) (t : ℝ) (ξ : Plane) : ℝ := ip n ξ*prof t ξ

theorem psi_continuous (n : Plane) (t : ℝ) (ht : 0<t) : Continuous (psi n t) := by
  unfold psi prof rad
  refine (ip_continuous n).mul
    (continuous_const.div (by fun_prop) (fun ξ => ?_))
  have := rad_pos t ht ξ
  unfold rad at this
  positivity

theorem abs_psi_le (n : Plane) (hn : ‖n‖=1) (t : ℝ) (ht : 0<t) (ξ : Plane) :
    |psi n t ξ|≤(3/(8*Real.pi))*StaticPlaneKernel.envelope t ξ := by
  have hr := rad_pos t ht ξ
  have hinner : abs (ip n ξ) ≤ ‖ξ‖ := by
    have := abs_ip_le n ξ
    rwa [hn, one_mul] at this
  have hprof : 0≤prof t ξ := prof_nonneg t ht ξ
  have hxt : ‖ξ‖*t≤(rad t ξ)^2/2 := by
    rw [rad_sq]
    nlinarith [sq_nonneg (‖ξ‖-t)]
  have h1 : |psi n t ξ|≤‖ξ‖*prof t ξ := by
    unfold psi
    rw [abs_mul, abs_of_nonneg hprof]
    exact mul_le_mul_of_nonneg_right hinner hprof
  have h2 : ‖ξ‖*prof t ξ≤(3/(8*Real.pi))*(rad t ξ)⁻¹^3 := by
    unfold prof
    have hp := Real.pi_pos
    rw [show ‖ξ‖*(3*t/(4*Real.pi*(rad t ξ)^5))=3*(‖ξ‖*t)/(4*Real.pi*(rad t ξ)^5) by ring]
    rw [div_le_iff₀ (by positivity)]
    calc 3*(‖ξ‖*t)≤3*((rad t ξ)^2/2) := by linarith
      _ = (3/(8*Real.pi))*(rad t ξ)⁻¹^3*(4*Real.pi*(rad t ξ)^5) := by
        field_simp
        ring
  have h3 := StaticPlaneKernel.inverse_cube_le_envelope t ht ξ (rad t ξ) (le_rad_right t ξ) (le_rad_left t ξ)
  calc |psi n t ξ|≤(3/(8*Real.pi))*(rad t ξ)⁻¹^3 := h1.trans h2
    _ ≤ (3/(8*Real.pi))*StaticPlaneKernel.envelope t ξ :=
      mul_le_mul_of_nonneg_left h3 (by have := Real.pi_pos; positivity)

theorem psi_integrable (n : Plane) (hn : ‖n‖=1) (t : ℝ) (ht : 0<t) : Integrable (psi n t) :=
  ((StaticPlaneKernel.envelope_integrable t ht).const_mul (3/(8*Real.pi))).mono'
    (psi_continuous n t ht).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      simpa only [Real.norm_eq_abs] using abs_psi_le n hn t ht ξ))

/-- Integral of the profile over the half disk of radius `S`. -/
def halfDisk (n : Plane) (t S : ℝ) : ℝ := ∫ ξ : Plane, (U n ∩ closedBall 0 S).indicator (psi n t) ξ

/-- Integral of the profile over the half plane. -/
def halfPlane (n : Plane) (t : ℝ) : ℝ := ∫ ξ : Plane, (U n).indicator (psi n t) ξ

theorem halfDisk_tendsto (n : Plane) (hn : ‖n‖=1) (t : ℝ) (ht : 0<t) :
    Tendsto (halfDisk n t) atTop (𝓝 (halfPlane n t)) := by
  unfold halfDisk halfPlane
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖psi n t ξ‖)
  · exact Filter.Eventually.of_forall (fun S =>
      ((psi_continuous n t ht).aestronglyMeasurable).indicator
        ((U_measurable n).inter measurableSet_closedBall))
  · exact Filter.Eventually.of_forall (fun S => Filter.Eventually.of_forall (fun ξ =>
      norm_indicator_le_norm_self _ _))
  · exact (psi_integrable n hn t ht).norm
  · refine Filter.Eventually.of_forall (fun ξ => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ‖ξ‖] with S hS
    by_cases hξ : ξ∈U n
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem (show ξ ∈ U n ∩ closedBall 0 S from ⟨hξ, by simpa using hS⟩)]
    · rw [Set.indicator_of_not_mem hξ, Set.indicator_of_not_mem (fun h => hξ h.1)]

theorem rad_smul (h a : ℝ) (ha : 0<a) (η : Plane) : rad (h*a) (a • η)=a*rad h η := by
  unfold rad
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have : (a*‖η‖)^2+(h*a)^2=a^2*(‖η‖^2+h^2) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

theorem prof_scale (h a : ℝ) (hh : 0<h) (ha : 0<a) (η : Plane) :
    prof (h*a) (a • η)=(a^4)⁻¹*prof h η := by
  have hr := rad_pos h hh η
  unfold prof
  rw [rad_smul h a ha]
  field_simp
  ring

theorem halfDisk_scale (n : Plane) (h a s : ℝ) (hh : 0<h) (ha : 0<a) :
    a*halfDisk n (h*a) s=halfDisk n h (s/a) := by
  have key : ∀ η : Plane, (U n ∩ closedBall 0 s).indicator (psi n (h*a)) (a • η)=
      (a^3)⁻¹*(U n ∩ closedBall 0 (s/a)).indicator (psi n h) η := by
    intro η
    have hmem : a • η∈U n ∩ closedBall (0 : Plane) s ↔ η∈U n ∩ closedBall (0 : Plane) (s/a) := by
      simp only [U, mem_inter_iff, mem_setOf_eq, mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha, ip_smul]
      rw [le_div_iff₀ ha, mul_comm ‖η‖ a]
      exact and_congr (mul_pos_iff_of_pos_left ha) Iff.rfl
    by_cases hη : η∈U n ∩ closedBall (0 : Plane) (s/a)
    · rw [Set.indicator_of_mem (hmem.mpr hη), Set.indicator_of_mem hη]
      simp only [psi, ip_smul, prof_scale h a hh ha]
      have h4 : a*(a^4)⁻¹=(a^3)⁻¹ := by field_simp; ring
      calc a*ip n η*((a^4)⁻¹*prof h η)=(a*(a^4)⁻¹)*(ip n η*prof h η) := by ring
        _ = (a^3)⁻¹*(ip n η*prof h η) := by rw [h4]
    · rw [Set.indicator_of_not_mem (fun h' => hη (hmem.mp h')), Set.indicator_of_not_mem hη]
      simp
  have hsm := Measure.integral_comp_smul (volume : Measure Plane)
    (fun ξ : Plane => (U n ∩ closedBall 0 s).indicator (psi n (h*a)) ξ) a
  simp only [key, integral_const_mul, finrank_euclideanSpace_fin] at hsm
  unfold halfDisk
  have ha3 : (a^3)≠0 := by positivity
  have ha2 : (a^2)⁻¹≥0 := by positivity
  rw [abs_of_nonneg (by positivity)] at hsm
  simp only [smul_eq_mul] at hsm
  field_simp at hsm
  refine mul_right_cancel₀ (pow_ne_zero 2 ha.ne') ?_
  rw [hsm]
  ring

theorem scaled_limit (n : Plane) (hn : ‖n‖=1) (h : ℝ) (hh : 0<h) (s : ℝ → ℝ)
    (hs : Tendsto (fun a => s a/a) (𝓝[>] 0) atTop) :
    Tendsto (fun a => a*halfDisk n (h*a) (s a)) (𝓝[>] 0) (𝓝 (halfPlane n h)) := by
  have hev : ∀ᶠ a : ℝ in 𝓝[>] 0, a*halfDisk n (h*a) (s a)=halfDisk n h (s a/a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact halfDisk_scale n h a (s a) hh ha
  exact ((halfDisk_tendsto n hn h hh).comp hs).congr' (hev.mono fun a ha => ha.symm)

theorem psi_neg (n : Plane) (t : ℝ) (ξ : Plane) : psi n t (-ξ)=-psi n t ξ := by
  unfold psi
  rw [ip_neg, prof_neg]
  ring

theorem psi_zero_of_ip_zero (n : Plane) (t : ℝ) (ξ : Plane) (h : ip n ξ=0) : psi n t ξ=0 := by
  unfold psi
  rw [h, zero_mul]

theorem neg_side (n : Plane) (t S : ℝ) (ht : 0<t) :
    (∫ ξ : Plane, ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 S).indicator (fun ξ => ‖psi n t ξ‖) ξ)=
      halfDisk n t S := by
  classical
  rw [← integral_neg_eq_self]
  unfold halfDisk
  congr 1
  funext ξ
  by_cases hnn : 0 < ip n ξ
  · have h1 : -ξ∈{ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) S ↔ ξ∈U n ∩ closedBall (0 : Plane) S := by
      simp only [mem_inter_iff, mem_setOf_eq, mem_closedBall, dist_zero_right, norm_neg, ip_neg, U]
      constructor
      · rintro ⟨_, h⟩; exact ⟨hnn, h⟩
      · rintro ⟨_, h⟩; exact ⟨by linarith, h⟩
    by_cases hb : ξ∈closedBall (0 : Plane) S
    · rw [Set.indicator_of_mem (h1.mpr ⟨hnn, hb⟩), Set.indicator_of_mem (show ξ∈U n ∩ closedBall 0 S from ⟨hnn, hb⟩)]
      rw [psi_neg, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
      unfold psi
      exact mul_nonneg hnn.le (prof_nonneg t ht ξ)
    · have h2 : -ξ∉{ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) S := by
        intro h
        apply hb
        simpa only [mem_closedBall, dist_zero_right, norm_neg] using h.2
      rw [Set.indicator_of_not_mem h2, Set.indicator_of_not_mem (fun h => hb h.2)]
  · have hle : ip n ξ≤0 := not_lt.mp hnn
    by_cases hb : ξ∈closedBall (0 : Plane) S
    · by_cases hz : ip n ξ=0
      · have hp : psi n t ξ=0 := psi_zero_of_ip_zero n t ξ hz
        have : psi n t (-ξ)=0 := by rw [psi_neg, hp, neg_zero]
        by_cases hm : -ξ∈{ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) S
        · rw [Set.indicator_of_mem hm, this, norm_zero, Set.indicator_apply]
          simp [hp]
        · exfalso
          apply hm
          refine ⟨?_, ?_⟩
          · simp [ip_neg, hz]
          · simpa only [mem_closedBall, dist_zero_right, norm_neg] using hb
      · have hneg : ip n ξ<0 := lt_of_le_of_ne hle hz
        have h2 : -ξ∉{ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) S := by
          intro h
          have := h.1
          simp only [mem_setOf_eq, ip_neg] at this
          exact this (by linarith)
        rw [Set.indicator_of_not_mem h2, Set.indicator_of_not_mem (fun h => hnn h.1)]
    · have h2 : -ξ∉{ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) S := by
        intro h
        apply hb
        simpa only [mem_closedBall, dist_zero_right, norm_neg] using h.2
      rw [Set.indicator_of_not_mem h2, Set.indicator_of_not_mem (fun h => hb h.2)]

/-- The passage integral of the local model profile over a section `D` that coincides near `c` with the half
plane `{q | 0 < ip n (q - c)}`. -/
theorem model_pos (D : Set Plane) (c : Plane) (n : Plane) (t s : ℝ)
    (hDs : D ∩ closedBall c s=(fun q => q-c) ⁻¹' (U n ∩ closedBall 0 s)) :
    (∫ q in D, (closedBall c s).indicator (fun q => psi n t (q-c)) q)=halfDisk n t s := by
  rw [setIntegral_indicator measurableSet_closedBall, hDs]
  have hm : MeasurableSet ((fun q : Plane => q-c) ⁻¹' (U n ∩ closedBall 0 s)) :=
    ((U_measurable n).inter measurableSet_closedBall).preimage (measurable_sub_const c)
  rw [← integral_indicator hm]
  have hq : ∀ q : Plane, ((fun q : Plane => q-c) ⁻¹' (U n ∩ closedBall 0 s)).indicator
      (fun q => psi n t (q-c)) q=(U n ∩ closedBall 0 s).indicator (psi n t) (q-c) := by
    intro q
    by_cases h : q-c∈U n ∩ closedBall (0 : Plane) s
    · rw [Set.indicator_of_mem (show q∈(fun q : Plane => q-c) ⁻¹' (U n ∩ closedBall 0 s) from h),
        Set.indicator_of_mem h]
    · rw [Set.indicator_of_not_mem (show q∉(fun q : Plane => q-c) ⁻¹' (U n ∩ closedBall 0 s) from h),
        Set.indicator_of_not_mem h]
  simp_rw [hq]
  exact integral_sub_right_eq_self (fun ξ => (U n ∩ closedBall 0 s).indicator (psi n t) ξ) c

/-- The bypass integral of the local model profile outside the section `D`. -/
theorem model_neg (D : Set Plane) (c : Plane) (n : Plane) (t s : ℝ) (ht : 0<t)
    (hDs : D ∩ closedBall c s=(fun q => q-c) ⁻¹' (U n ∩ closedBall 0 s)) :
    (∫ q in Dᶜ, ‖(closedBall c s).indicator (fun q => psi n t (q-c)) q‖)=halfDisk n t s := by
  have hset : Dᶜ ∩ closedBall c s=(fun q : Plane => q-c) ⁻¹' ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s) := by
    ext q
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_setOf_eq, mem_closedBall, dist_zero_right, sub_zero,
      dist_eq_norm]
    constructor
    · rintro ⟨hD, hb⟩
      refine ⟨fun hp => hD ?_, hb⟩
      have : q∈(fun q : Plane => q-c) ⁻¹' (U n ∩ closedBall 0 s) := by
        refine ⟨hp, ?_⟩
        simpa only [mem_closedBall, dist_zero_right] using hb
      rw [← hDs] at this
      exact this.1
    · rintro ⟨hp, hb⟩
      refine ⟨fun hD => hp ?_, hb⟩
      have : q∈D ∩ closedBall c s := ⟨hD, by simpa only [mem_closedBall, dist_eq_norm] using hb⟩
      rw [hDs] at this
      exact this.1
  have h1 : (∫ q in Dᶜ, ‖(closedBall c s).indicator (fun q => psi n t (q-c)) q‖)=
      ∫ q in Dᶜ, (closedBall c s).indicator (fun q => ‖psi n t (q-c)‖) q := by
    congr 1
    funext q
    exact norm_indicator_eq_indicator_norm _ _
  rw [h1, setIntegral_indicator measurableSet_closedBall, hset]
  have hm : MeasurableSet ((fun q : Plane => q-c) ⁻¹' ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s)) :=
    ((U_measurable n).compl.inter measurableSet_closedBall).preimage (measurable_sub_const c)
  rw [← integral_indicator hm]
  have hq : ∀ q : Plane, ((fun q : Plane => q-c) ⁻¹' ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s)).indicator
      (fun q => ‖psi n t (q-c)‖) q=({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s).indicator
        (fun ξ => ‖psi n t ξ‖) (q-c) := by
    intro q
    by_cases h : q-c∈({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall (0 : Plane) s)
    · rw [Set.indicator_of_mem (show q∈(fun q : Plane => q-c) ⁻¹' ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s)
        from h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_not_mem (show q∉(fun q : Plane => q-c) ⁻¹'
        ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s) from h), Set.indicator_of_not_mem h]
  simp_rw [hq]
  rw [integral_sub_right_eq_self (fun ξ => ({ξ : Plane | ¬ 0 < ip n ξ} ∩ closedBall 0 s).indicator
    (fun ξ => ‖psi n t ξ‖) ξ) c]
  exact neg_side n t s ht

end OQ14.RestrictedTEDipoleProfile
#print axioms OQ14.RestrictedTEDipoleProfile.ip_smul
#print axioms OQ14.RestrictedTEDipoleProfile.ip_neg
#print axioms OQ14.RestrictedTEDipoleProfile.ip_continuous
#print axioms OQ14.RestrictedTEDipoleProfile.abs_ip_le
#print axioms OQ14.RestrictedTEDipoleProfile.norm_sq_plane
#print axioms OQ14.RestrictedTEDipoleProfile.norm_sq_space
#print axioms OQ14.RestrictedTEDipoleProfile.norm_diff
#print axioms OQ14.RestrictedTEDipoleProfile.rad_pos
#print axioms OQ14.RestrictedTEDipoleProfile.le_rad_left
#print axioms OQ14.RestrictedTEDipoleProfile.le_rad_right
#print axioms OQ14.RestrictedTEDipoleProfile.rad_sq
#print axioms OQ14.RestrictedTEDipoleProfile.prof_nonneg
#print axioms OQ14.RestrictedTEDipoleProfile.prof_neg
#print axioms OQ14.RestrictedTEDipoleProfile.phiHessian_static_off
#print axioms OQ14.RestrictedTEDipoleProfile.diff_tangent
#print axioms OQ14.RestrictedTEDipoleProfile.diff_normal
#print axioms OQ14.RestrictedTEDipoleProfile.hess_tangent_normal
#print axioms OQ14.RestrictedTEDipoleProfile.U_measurable
#print axioms OQ14.RestrictedTEDipoleProfile.psi_continuous
#print axioms OQ14.RestrictedTEDipoleProfile.abs_psi_le
#print axioms OQ14.RestrictedTEDipoleProfile.psi_integrable
#print axioms OQ14.RestrictedTEDipoleProfile.halfDisk_tendsto
#print axioms OQ14.RestrictedTEDipoleProfile.rad_smul
#print axioms OQ14.RestrictedTEDipoleProfile.prof_scale
#print axioms OQ14.RestrictedTEDipoleProfile.halfDisk_scale
#print axioms OQ14.RestrictedTEDipoleProfile.scaled_limit
#print axioms OQ14.RestrictedTEDipoleProfile.psi_neg
#print axioms OQ14.RestrictedTEDipoleProfile.psi_zero_of_ip_zero
#print axioms OQ14.RestrictedTEDipoleProfile.neg_side
#print axioms OQ14.RestrictedTEDipoleProfile.model_pos
#print axioms OQ14.RestrictedTEDipoleProfile.model_neg
