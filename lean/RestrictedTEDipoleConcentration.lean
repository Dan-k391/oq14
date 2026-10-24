import RestrictedTEDipoleProfile
import FinitePlaneDipole
import RestrictedTEPassageTransfer

/-! L1 concentration of the exact finite-ball dipole flux: for dipoles at heights `h_l a` above fixed plane
points `c_l`, radius `ρ a`, strengths `P_l = Λ a⁻¹ (e_l ẑ + δ_l)` and a background magnetic field `a⁻¹ H0`, the
whole-plane flux differs from the local jet model by an explicit quantity that tends to zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEDipoleConcentration
open MeasureTheory Metric Set Filter OQ14.RestrictedTEDipoleProfile
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane
abbrev Vec := FinitePlaneDipole.Vector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Volume coefficient of the dipole balls: `vol (ball x (ρ a)) = Vb ρ * a^3`. -/
def Vb (ρ : ℝ) : ℝ := ρ^3*(Real.pi*4/3)

theorem vol_ball (x : Space) (ρ a : ℝ) (hρ : 0≤ρ) (ha : 0≤a) :
    volume.real (ball x (ρ*a))=Vb ρ*a^3 := by
  simp only [measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg hρ ha), ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  unfold Vb
  ring

theorem cross_two (u v : Fin 3 → ℂ) : crossProduct u v 2=u 0*v 1-u 1*v 0 := by
  rw [cross_apply]
  rfl

/-- Dipole centres above the plane points `c l`. -/
def centre (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (l : ι) : Space := abovePoint (c l) (h l*a)

/-- The flux density of the dipoles against a background magnetic field `Hf`. -/
def fluxFn (c : ι → Plane) (h : ι → ℝ) (ρ a : ℝ) (P : ι → Vec) (Hf : Space → Fin 3 → ℂ) (q : Plane) : ℂ :=
  crossProduct (FinitePlaneDipole.dipoles (centre c h a) (fun _ => ρ*a) P (MaxwellPlaneTail.planePoint q))
    (fun j => conj (Hf (MaxwellPlaneTail.planePoint q) j)) 2

/-- Static Hessian entry at the plane point `q` for the dipole `l`. -/
def hess (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (l : ι) (q : Plane) (i j : Fin 3) : ℂ :=
  GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-centre c h a l) i j

/-- Main (normal-dipole) part of the local flux of the dipole `l`. -/
def mainPart (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (e : ι → ℂ) (H0 : Space → Fin 3 → ℂ) (l : ι) (q : Plane) : ℂ :=
  e l*(hess c h a l q 0 2*conj (H0 (MaxwellPlaneTail.planePoint q) 1)-
    hess c h a l q 1 2*conj (H0 (MaxwellPlaneTail.planePoint q) 0))

/-- The correction part of the local flux of the dipole `l` (all strength errors). -/
def corrPart (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (δ : ι → Fin 3 → ℂ) (H0 : Space → Fin 3 → ℂ) (l : ι)
    (q : Plane) : ℂ :=
  ∑ j : Fin 3, δ l j*(hess c h a l q 0 j*conj (H0 (MaxwellPlaneTail.planePoint q) 1)-
    hess c h a l q 1 j*conj (H0 (MaxwellPlaneTail.planePoint q) 0))

/-- The local model with the background replaced by the plane jets `η0, η1` inside the radius-`s` disks. -/
def modelFn (c : ι → Plane) (h : ι → ℝ) (ρ a s : ℝ) (Λ : ℂ) (e : ι → ℂ) (η0 η1 : ι → ℂ) (q : Plane) : ℂ :=
  ((Vb ρ*a : ℝ) : ℂ)*Λ*∑ l, (closedBall (c l) s).indicator
    (fun q => e l*(hess c h a l q 0 2*conj (η1 l)-hess c h a l q 1 2*conj (η0 l))) q

theorem flux_decomp (c : ι → Plane) (h : ι → ℝ) (ρ a : ℝ) (ha : 0<a) (hρ : 0≤ρ) (Λ : ℂ)
    (e : ι → ℂ) (δ : ι → Fin 3 → ℂ) (P : ι → Vec) (H0 : Space → Fin 3 → ℂ)
    (hP : ∀ l j, P l j=Λ*((a : ℂ)⁻¹)*((if j=2 then e l else 0)+δ l j)) (q : Plane) :
    fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j) q=
      ((Vb ρ*a : ℝ) : ℂ)*Λ*∑ l, (mainPart c h a e H0 l q+corrPart c h a δ H0 l q) := by
  unfold fluxFn
  rw [cross_two]
  simp only [FinitePlaneDipole.dipoles, StaticBallPlaneDipole.dipole, centre, map_mul, Complex.conj_ofReal]
  have hv : ∀ l, volume.real (ball (abovePoint (c l) (h l*a)) (ρ*a))=Vb ρ*a^3 := fun l =>
    vol_ball _ ρ a hρ ha.le
  simp only [hv, hP, Fin.sum_univ_three]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold mainPart corrPart hess centre
  simp only [Fin.sum_univ_three, if_true, if_false, Fin.reduceEq, zero_add, add_zero]
  have haC : (a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  push_cast
  field_simp
  ring

theorem fluxFn_sub_model (c : ι → Plane) (h : ι → ℝ) (ρ a s : ℝ) (ha : 0<a) (hρ : 0≤ρ) (Λ : ℂ)
    (e : ι → ℂ) (δ : ι → Fin 3 → ℂ) (P : ι → Vec) (H0 : Space → Fin 3 → ℂ) (η0 η1 : ι → ℂ)
    (hP : ∀ l j, P l j=Λ*((a : ℂ)⁻¹)*((if j=2 then e l else 0)+δ l j)) (q : Plane) :
    fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j) q-modelFn c h ρ a s Λ e η0 η1 q=
      ((Vb ρ*a : ℝ) : ℂ)*Λ*∑ l, (corrPart c h a δ H0 l q+
        (mainPart c h a e H0 l q-(closedBall (c l) s).indicator
          (fun q => e l*(hess c h a l q 0 2*conj (η1 l)-hess c h a l q 1 2*conj (η0 l))) q)) := by
  rw [flux_decomp c h ρ a ha hρ Λ e δ P H0 hP q]
  unfold modelFn
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring


theorem above_normal (c : Plane) (t : ℝ) : (abovePoint c t) 2=t := by
  simp [abovePoint]

theorem diff_ne (q c : Plane) (t : ℝ) (ht : 0<t) : MaxwellPlaneTail.planePoint q-abovePoint c t≠0 := by
  intro hz
  have := diff_normal q c t
  rw [hz] at this
  simp at this
  linarith

theorem hess_bound (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (l : ι) (q : Plane)
    (hq : 0<‖q-c l‖) (i j : Fin 3) :
    ‖hess c h a l q i j‖≤(1/Real.pi)*(‖q-c l‖⁻¹)^3 := by
  have hpos : 0<h l*a := mul_pos (hh l) ha
  have hz := diff_ne q (c l) (h l*a) hpos
  unfold hess centre
  refine (StaticPlaneKernel.static_hessian_bound _ hz i j).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [norm_diff]
  have hr := rad_pos (h l*a) hpos (q-c l)
  have hle := le_rad_left (h l*a) (q-c l)
  exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) ((inv_le_inv₀ hr hq).mpr hle) 3

theorem hess_integrable_mass (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (l : ι)
    (i j : Fin 3) :
    Integrable (fun q => ‖hess c h a l q i j‖) ∧ (∫ q, ‖hess c h a l q i j‖)≤3/(h l*a) := by
  have hpos : 0<h l*a := mul_pos (hh l) ha
  have hy : h l*a≤|(centre c h a l) 2| := by
    unfold centre
    rw [above_normal, abs_of_pos hpos]
  exact ⟨(StaticPlaneKernel.plane_kernel_integrable _ hpos _ hy i j).norm,
    StaticPlaneKernel.plane_kernel_mass _ hpos _ hy i j⟩

theorem bound_cross (d X Y u v : ℂ) (ωδ M : ℝ) (hd : ‖d‖≤ωδ) (hu : ‖u‖≤M) (hv : ‖v‖≤M) :
    ‖d*(X*conj u-Y*conj v)‖≤ωδ*M*(‖X‖+‖Y‖) := by
  have h0 : 0≤ωδ := (norm_nonneg d).trans hd
  have hM : 0≤M := (norm_nonneg u).trans hu
  rw [norm_mul]
  have h1 : ‖X*conj u-Y*conj v‖≤‖X‖*M+‖Y‖*M := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)
  calc ‖d‖*‖X*conj u-Y*conj v‖≤ωδ*(‖X‖*M+‖Y‖*M) :=
        mul_le_mul hd h1 (norm_nonneg _) h0
    _ = ωδ*M*(‖X‖+‖Y‖) := by ring

theorem bound_diff (e X Y u0 u1 w0 w1 : ℂ) (ωH : ℝ) (h0 : ‖u0-w0‖≤ωH) (h1 : ‖u1-w1‖≤ωH) :
    ‖e*(X*conj u1-Y*conj u0)-e*(X*conj w1-Y*conj w0)‖≤‖e‖*ωH*(‖X‖+‖Y‖) := by
  have hω : 0≤ωH := (norm_nonneg _).trans h0
  have : e*(X*conj u1-Y*conj u0)-e*(X*conj w1-Y*conj w0)=
      e*(X*conj (u1-w1)-Y*conj (u0-w0)) := by
    simp only [map_sub]
    ring
  rw [this, norm_mul]
  have h2 : ‖X*conj (u1-w1)-Y*conj (u0-w0)‖≤‖X‖*ωH+‖Y‖*ωH := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
  calc ‖e‖*‖X*conj (u1-w1)-Y*conj (u0-w0)‖≤‖e‖*(‖X‖*ωH+‖Y‖*ωH) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖e‖*ωH*(‖X‖+‖Y‖) := by ring

theorem bound_outside (e X Y u0 u1 : ℂ) (M : ℝ) (hu0 : ‖u0‖≤M) (hu1 : ‖u1‖≤M) :
    ‖e*(X*conj u1-Y*conj u0)‖≤‖e‖*M*(‖X‖+‖Y‖) := by
  have := bound_cross e X Y u1 u0 ‖e‖ M le_rfl hu1 hu0
  rw [norm_mul] at this ⊢
  have h1 : ‖X*conj u1-Y*conj u0‖≤M*(‖X‖+‖Y‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left hu1 (norm_nonneg X), mul_le_mul_of_nonneg_left hu0 (norm_nonneg Y)]
  calc ‖e‖*‖X*conj u1-Y*conj u0‖≤‖e‖*(M*(‖X‖+‖Y‖)) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖e‖*M*(‖X‖+‖Y‖) := by ring


/-- Majorant of the correction terms. -/
def g1 (c : ι → Plane) (h : ι → ℝ) (a ωδ M : ℝ) (l : ι) (q : Plane) : ℝ :=
  ωδ*M*∑ j : Fin 3, (‖hess c h a l q 0 j‖+‖hess c h a l q 1 j‖)

/-- Majorant of the jet-replacement error. -/
def g2 (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (e : ι → ℂ) (ωH : ℝ) (l : ι) (q : Plane) : ℝ :=
  ‖e l‖*ωH*(‖hess c h a l q 0 2‖+‖hess c h a l q 1 2‖)

/-- Majorant of the far tail. -/
def g3 (c : ι → Plane) (e : ι → ℂ) (M s : ℝ) (l : ι) (q : Plane) : ℝ :=
  (2*‖e l‖*M/Real.pi)*PlaneInverseCube.profile s ‖q-c l‖

theorem profile_eq (s t : ℝ) (hst : s<t) : PlaneInverseCube.profile s t=(t⁻¹)^3 := by
  simp [PlaneInverseCube.profile, Set.indicator, hst]

theorem profile_nonneg (s t : ℝ) (hs : 0≤s) : 0≤PlaneInverseCube.profile s t := by
  unfold PlaneInverseCube.profile
  exact Set.indicator_nonneg (fun t ht => by
    simp only [mem_Ioi] at ht
    have : 0<t := hs.trans_lt ht
    positivity) t

theorem corr_le (c : ι → Plane) (h : ι → ℝ) (a ωδ M : ℝ) (δ : ι → Fin 3 → ℂ) (H0 : Space → Fin 3 → ℂ)
    (hδ : ∀ l j, ‖δ l j‖≤ωδ) (hM : ∀ x j, ‖H0 x j‖≤M) (l : ι) (q : Plane) :
    ‖corrPart c h a δ H0 l q‖≤g1 c h a ωδ M l q := by
  unfold corrPart g1
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  exact bound_cross (δ l j) (hess c h a l q 0 j) (hess c h a l q 1 j) _ _ ωδ M (hδ l j) (hM _ 1) (hM _ 0)

theorem main_le (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (e : ι → ℂ)
    (H0 : Space → Fin 3 → ℂ) (η0 η1 : ι → ℂ) (M ωH s : ℝ) (hs : 0<s)
    (hM : ∀ x j, ‖H0 x j‖≤M)
    (hjet : ∀ l q, q∈closedBall (c l) s → ‖H0 (MaxwellPlaneTail.planePoint q) 0-η0 l‖≤ωH ∧
      ‖H0 (MaxwellPlaneTail.planePoint q) 1-η1 l‖≤ωH) (l : ι) (q : Plane) :
    ‖mainPart c h a e H0 l q-(closedBall (c l) s).indicator
      (fun q => e l*(hess c h a l q 0 2*conj (η1 l)-hess c h a l q 1 2*conj (η0 l))) q‖≤
      g2 c h a e ωH l q+g3 c e M s l q := by
  have hM0 : 0≤M := (norm_nonneg _).trans (hM 0 0)
  by_cases hq : q∈closedBall (c l) s
  · rw [Set.indicator_of_mem hq]
    obtain ⟨h0, h1⟩ := hjet l q hq
    have hb := bound_diff (e l) (hess c h a l q 0 2) (hess c h a l q 1 2) _ _ (η0 l) (η1 l) ωH h0 h1
    have hg3 : 0≤g3 c e M s l q := by
      unfold g3
      exact mul_nonneg (by positivity) (profile_nonneg s _ hs.le)
    unfold mainPart g2
    linarith
  · rw [Set.indicator_of_not_mem hq]
    have hqs : s<‖q-c l‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hq
    have hqp : 0<‖q-c l‖ := hs.trans hqs
    have hb := bound_outside (e l) (hess c h a l q 0 2) (hess c h a l q 1 2) (H0 (MaxwellPlaneTail.planePoint q) 0) (H0 (MaxwellPlaneTail.planePoint q) 1) M (hM _ 0) (hM _ 1)
    have hx := hess_bound c h hh a ha l q hqp 0 2
    have hy := hess_bound c h hh a ha l q hqp 1 2
    have hg2 : 0≤g2 c h a e ωH l q := by
      unfold g2
      have : 0≤ωH := by
        obtain ⟨h0, _⟩ := hjet l (c l) (mem_closedBall_self hs.le)
        exact (norm_nonneg _).trans h0
      positivity
    have hg3 : g3 c e M s l q=(2*‖e l‖*M/Real.pi)*(‖q-c l‖⁻¹)^3 := by
      unfold g3
      rw [profile_eq s _ hqs]
    rw [sub_zero]
    unfold mainPart
    refine hb.trans ?_
    have h3 : ‖e l‖*M*(‖hess c h a l q 0 2‖+‖hess c h a l q 1 2‖)≤g3 c e M s l q := by
      rw [hg3]
      have hp : 0≤‖e l‖*M := mul_nonneg (norm_nonneg _) hM0
      calc ‖e l‖*M*(‖hess c h a l q 0 2‖+‖hess c h a l q 1 2‖)≤‖e l‖*M*((1/Real.pi)*(‖q-c l‖⁻¹)^3+
            (1/Real.pi)*(‖q-c l‖⁻¹)^3) := mul_le_mul_of_nonneg_left (add_le_add hx hy) hp
        _ = (2*‖e l‖*M/Real.pi)*(‖q-c l‖⁻¹)^3 := by ring
    linarith


theorem g1_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (ωδ M : ℝ) (l : ι) :
    Integrable (g1 c h a ωδ M l) := by
  unfold g1
  exact (integrable_finset_sum _ (fun j _ =>
    (hess_integrable_mass c h hh a ha l 0 j).1.add (hess_integrable_mass c h hh a ha l 1 j).1)).const_mul _

theorem g2_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (e : ι → ℂ)
    (ωH : ℝ) (l : ι) : Integrable (g2 c h a e ωH l) := by
  unfold g2
  exact ((hess_integrable_mass c h hh a ha l 0 2).1.add (hess_integrable_mass c h hh a ha l 1 2).1).const_mul _

theorem profile_translate_integrable (s : ℝ) (hs : 0<s) (c : Plane) :
    Integrable (fun q : Plane => PlaneInverseCube.profile s ‖q-c‖) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure Plane) (-c)).integrable_comp
      (PlaneInverseCube.inverse_cube_integrable s hs).aestronglyMeasurable |>.mpr
      (PlaneInverseCube.inverse_cube_integrable s hs)

theorem g3_integrable (c : ι → Plane) (e : ι → ℂ) (M s : ℝ) (hs : 0<s) (l : ι) :
    Integrable (g3 c e M s l) := by
  unfold g3
  exact (profile_translate_integrable s hs (c l)).const_mul _

theorem g1_integral_le (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (ωδ M : ℝ)
    (hω : 0≤ωδ) (hM : 0≤M) (l : ι) :
    (∫ q, g1 c h a ωδ M l q)≤18*M*ωδ/(h l*a) := by
  have hI (i j : Fin 3) := hess_integrable_mass c h hh a ha l i j
  have hpos : 0<h l*a := mul_pos (hh l) ha
  unfold g1
  rw [integral_const_mul, integral_finset_sum (Finset.univ : Finset (Fin 3))
    (f := fun (j : Fin 3) (q : Plane) => ‖hess c h a l q 0 j‖+‖hess c h a l q 1 j‖)
    (fun j _ => (hI 0 j).1.add (hI 1 j).1)]
  have hs : (∑ j : Fin 3, ∫ q, (‖hess c h a l q 0 j‖+‖hess c h a l q 1 j‖))≤∑ j : Fin 3, (3/(h l*a)+3/(h l*a)) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [integral_add (hI 0 j).1 (hI 1 j).1]
    exact add_le_add (hI 0 j).2 (hI 1 j).2
  have hc : (∑ j : Fin 3, (3/(h l*a)+3/(h l*a)))=18/(h l*a) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  calc ωδ*M*(∑ j : Fin 3, ∫ q, (‖hess c h a l q 0 j‖+‖hess c h a l q 1 j‖))≤ωδ*M*(18/(h l*a)) :=
        mul_le_mul_of_nonneg_left (hs.trans_eq hc) (mul_nonneg hω hM)
    _ = 18*M*ωδ/(h l*a) := by ring

theorem g2_integral_le (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (e : ι → ℂ)
    (ωH : ℝ) (hω : 0≤ωH) (l : ι) :
    (∫ q, g2 c h a e ωH l q)≤6*‖e l‖*ωH/(h l*a) := by
  have hI (i j : Fin 3) := hess_integrable_mass c h hh a ha l i j
  have hpos : 0<h l*a := mul_pos (hh l) ha
  unfold g2
  rw [integral_const_mul, integral_add (hI 0 2).1 (hI 1 2).1]
  have h2 : (∫ q, ‖hess c h a l q 0 2‖)+(∫ q, ‖hess c h a l q 1 2‖)≤3/(h l*a)+3/(h l*a) :=
    add_le_add (hI 0 2).2 (hI 1 2).2
  calc ‖e l‖*ωH*((∫ q, ‖hess c h a l q 0 2‖)+(∫ q, ‖hess c h a l q 1 2‖))≤
        ‖e l‖*ωH*(3/(h l*a)+3/(h l*a)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (norm_nonneg _) hω)
    _ = 6*‖e l‖*ωH/(h l*a) := by ring

theorem g3_integral (c : ι → Plane) (e : ι → ℂ) (M s : ℝ) (hs : 0<s) (l : ι) :
    (∫ q, g3 c e M s l q)=(2*‖e l‖*M/Real.pi)*(PlaneInverseCube.diskConstant/s) := by
  unfold g3
  rw [integral_const_mul]
  congr 1
  rw [integral_sub_right_eq_self (fun x : Plane => PlaneInverseCube.profile s ‖x‖) (c l)]
  exact PlaneInverseCube.inverse_cube_integral s hs

/-- The explicit L1 concentration bound. -/
theorem concentration_bound (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a s : ℝ) (hρ : 0≤ρ)
    (ha : 0<a) (hs : 0<s) (Λ : ℂ) (e : ι → ℂ) (δ : ι → Fin 3 → ℂ) (P : ι → Vec)
    (H0 : Space → Fin 3 → ℂ) (η0 η1 : ι → ℂ) (M ωδ ωH : ℝ) (hωδ : 0≤ωδ) (hωH : 0≤ωH)
    (hP : ∀ l j, P l j=Λ*((a : ℂ)⁻¹)*((if j=2 then e l else 0)+δ l j))
    (hM : ∀ x j, ‖H0 x j‖≤M) (hδ : ∀ l j, ‖δ l j‖≤ωδ)
    (hjet : ∀ l q, q∈closedBall (c l) s → ‖H0 (MaxwellPlaneTail.planePoint q) 0-η0 l‖≤ωH ∧
      ‖H0 (MaxwellPlaneTail.planePoint q) 1-η1 l‖≤ωH) :
    (∫ q, ‖fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j) q-modelFn c h ρ a s Λ e η0 η1 q‖)≤
      Vb ρ*‖Λ‖*∑ l, ((18*M*ωδ+6*‖e l‖*ωH)/h l+a*(2*‖e l‖*M/Real.pi)*PlaneInverseCube.diskConstant/s) := by
  have hM0 : 0≤M := (norm_nonneg _).trans (hM 0 0)
  have hVb : 0≤Vb ρ := by unfold Vb; positivity
  let L : ℝ := ‖((Vb ρ*a : ℝ) : ℂ)*Λ‖
  have hL : L=Vb ρ*a*‖Λ‖ := by
    simp only [L, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hVb, abs_of_pos ha]
  have hL0 : 0≤L := norm_nonneg _
  let G : Plane → ℝ := fun q => L*∑ l, (g1 c h a ωδ M l q+g2 c h a e ωH l q+g3 c e M s l q)
  have hGi : Integrable G :=
    (integrable_finset_sum _ (fun l _ => ((g1_integrable c h hh a ha ωδ M l).add
      (g2_integrable c h hh a ha e ωH l)).add (g3_integrable c e M s hs l))).const_mul L
  have hpt : ∀ q, ‖fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j) q-modelFn c h ρ a s Λ e η0 η1 q‖≤G q := by
    intro q
    rw [fluxFn_sub_model c h ρ a s ha hρ Λ e δ P H0 η0 η1 hP q, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => ?_))) hL0
    refine (norm_add_le _ _).trans ?_
    have h1 := corr_le c h a ωδ M δ H0 hδ hM l q
    have h2 := main_le c h hh a ha e H0 η0 η1 M ωH s hs hM hjet l q
    linarith
  have hint : (∫ q, ‖fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j) q-modelFn c h ρ a s Λ e η0 η1 q‖)≤∫ q, G q :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun q => norm_nonneg _)) hGi
      (Filter.Eventually.of_forall hpt)
  refine hint.trans ?_
  have hG : (∫ q, G q)=L*∑ l, ((∫ q, g1 c h a ωδ M l q)+(∫ q, g2 c h a e ωH l q)+(∫ q, g3 c e M s l q)) := by
    simp only [G]
    rw [integral_const_mul, integral_finset_sum (Finset.univ : Finset ι)
      (f := fun (l : ι) (q : Plane) => g1 c h a ωδ M l q+g2 c h a e ωH l q+g3 c e M s l q)
      (fun l _ => ((g1_integrable c h hh a ha ωδ M l).add
      (g2_integrable c h hh a ha e ωH l)).add (g3_integrable c e M s hs l))]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hA : Integrable (fun q => g1 c h a ωδ M l q+g2 c h a e ωH l q) :=
      (g1_integrable c h hh a ha ωδ M l).add (g2_integrable c h hh a ha e ωH l)
    rw [integral_add hA (g3_integrable c e M s hs l), integral_add (g1_integrable c h hh a ha ωδ M l)
      (g2_integrable c h hh a ha e ωH l)]
  rw [hG, hL]
  have hsum : (∑ l, ((∫ q, g1 c h a ωδ M l q)+(∫ q, g2 c h a e ωH l q)+(∫ q, g3 c e M s l q)))≤
      ∑ l, ((18*M*ωδ+6*‖e l‖*ωH)/(h l*a)+(2*‖e l‖*M/Real.pi)*(PlaneInverseCube.diskConstant/s)) := by
    refine Finset.sum_le_sum (fun l _ => ?_)
    have h1 := g1_integral_le c h hh a ha ωδ M hωδ hM0 l
    have h2 := g2_integral_le c h hh a ha e ωH hωH l
    rw [g3_integral c e M s hs l]
    have : (18*M*ωδ+6*‖e l‖*ωH)/(h l*a)=18*M*ωδ/(h l*a)+6*‖e l‖*ωH/(h l*a) := by ring
    rw [this]
    linarith
  calc Vb ρ*a*‖Λ‖*(∑ l, ((∫ q, g1 c h a ωδ M l q)+(∫ q, g2 c h a e ωH l q)+(∫ q, g3 c e M s l q)))≤
        Vb ρ*a*‖Λ‖*∑ l, ((18*M*ωδ+6*‖e l‖*ωH)/(h l*a)+(2*‖e l‖*M/Real.pi)*(PlaneInverseCube.diskConstant/s)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg hVb ha.le) (norm_nonneg _))
    _ = Vb ρ*‖Λ‖*∑ l, ((18*M*ωδ+6*‖e l‖*ωH)/h l+a*(2*‖e l‖*M/Real.pi)*PlaneInverseCube.diskConstant/s) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        have hl := (hh l).ne'
        have has := ha.ne'
        have hss := hs.ne'
        field_simp
        ring


theorem ip_apply (n ξ : Plane) : ip n ξ=n 0*ξ 0+n 1*ξ 1 := by
  unfold ip
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- With the background jets `η = m τ` parallel to the tangent `τ = (-n₁, n₀)`, the local model profile is
`-(e conj m) * psi n (h a) (q - c)`. -/
theorem term_eq (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (e m : ι → ℂ)
    (n : ι → Plane) (η0 η1 : ι → ℂ) (hη0 : ∀ l, η0 l=-(m l)*((n l 1 : ℝ) : ℂ))
    (hη1 : ∀ l, η1 l=m l*((n l 0 : ℝ) : ℂ)) (l : ι) (q : Plane) :
    e l*(hess c h a l q 0 2*conj (η1 l)-hess c h a l q 1 2*conj (η0 l))=
      -(e l*conj (m l))*((psi (n l) (h l*a) (q-c l) : ℝ) : ℂ) := by
  have hpos : 0<h l*a := mul_pos (hh l) ha
  have h0 := hess_tangent_normal q (c l) (h l*a) hpos 0
  have h1 := hess_tangent_normal q (c l) (h l*a) hpos 1
  have e0 : hess c h a l q 0 2=((-(prof (h l*a) (q-c l)*(q-c l) 0) : ℝ) : ℂ) := h0
  have e1 : hess c h a l q 1 2=((-(prof (h l*a) (q-c l)*(q-c l) 1) : ℝ) : ℂ) := h1
  rw [e0, e1, hη0 l, hη1 l]
  unfold psi
  rw [ip_apply]
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  push_cast
  simp only [PiLp.sub_apply]
  ring

theorem norm_sum_disjoint {κ : Type*} [Fintype κ] (f : κ → ℂ) (hf : ∀ l m, l≠m → f l=0 ∨ f m=0) :
    ‖∑ l, f l‖=∑ l, ‖f l‖ := by
  classical
  by_cases h : ∃ l, f l≠0
  · obtain ⟨l0, hl0⟩ := h
    have hz : ∀ m, m≠l0 → f m=0 := fun m hm => (hf m l0 hm).resolve_right hl0
    rw [Finset.sum_eq_single l0 (fun m _ hm => hz m hm) (by simp),
      Finset.sum_eq_single l0 (fun m _ hm => by rw [hz m hm, norm_zero]) (by simp)]
  · push_neg at h
    simp [h]

/-- The real local profile of the dipole `l`, cut off at the radius `s`. -/
def Tl (c : ι → Plane) (h : ι → ℝ) (a s : ℝ) (n : ι → Plane) (l : ι) (q : Plane) : ℝ :=
  (closedBall (c l) s).indicator (fun q => psi (n l) (h l*a) (q-c l)) q

theorem psi_translate_integrable (n : Plane) (hn : ‖n‖=1) (t : ℝ) (ht : 0<t) (c : Plane) :
    Integrable (fun q : Plane => psi n t (q-c)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure Plane) (-c)).integrable_comp
      (psi_integrable n hn t ht).aestronglyMeasurable |>.mpr (psi_integrable n hn t ht)

theorem Tl_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a s : ℝ) (ha : 0<a) (n : ι → Plane)
    (hn : ∀ l, ‖n l‖=1) (l : ι) : Integrable (Tl c h a s n l) := by
  unfold Tl
  exact (psi_translate_integrable (n l) (hn l) (h l*a) (mul_pos (hh l) ha) (c l)).indicator
    measurableSet_closedBall

theorem model_eq (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a s : ℝ) (ha : 0<a) (Λ : ℂ)
    (e m : ι → ℂ) (n : ι → Plane) (η0 η1 : ι → ℂ)
    (hη0 : ∀ l, η0 l=-(m l)*((n l 1 : ℝ) : ℂ)) (hη1 : ∀ l, η1 l=m l*((n l 0 : ℝ) : ℂ)) (q : Plane) :
    modelFn c h ρ a s Λ e η0 η1 q=
      (a : ℂ)*∑ l, (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)))*((Tl c h a s n l q : ℝ) : ℂ) := by
  unfold modelFn
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases hq : q∈closedBall (c l) s
  · rw [Set.indicator_of_mem hq, term_eq c h hh a ha e m n η0 η1 hη0 hη1 l q]
    unfold Tl
    rw [Set.indicator_of_mem hq]
    push_cast
    ring
  · rw [Set.indicator_of_not_mem hq]
    unfold Tl
    rw [Set.indicator_of_not_mem hq]
    simp

/-- Local-model passage over a section `D` which is a half plane near each dipole position. -/
theorem model_passage (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a s : ℝ) (ha : 0<a) (Λ : ℂ)
    (e m : ι → ℂ) (n : ι → Plane) (η0 η1 : ι → ℂ)
    (hη0 : ∀ l, η0 l=-(m l)*((n l 1 : ℝ) : ℂ)) (hη1 : ∀ l, η1 l=m l*((n l 0 : ℝ) : ℂ))
    (hn : ∀ l, ‖n l‖=1) (D : Set Plane)
    (hDs : ∀ l, D ∩ closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s)) :
    OQ14.RestrictedTEPassageTransfer.passage volume D (modelFn c h ρ a s Λ e η0 η1)=
      a*∑ l, (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l))).re*halfDisk (n l) (h l*a) s := by
  unfold OQ14.RestrictedTEPassageTransfer.passage
  simp_rw [model_eq c h hh ρ a s ha Λ e m n η0 η1 hη0 hη1]
  have hI (l : ι) : IntegrableOn (fun q => (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)))*((Tl c h a s n l q : ℝ) : ℂ)) D :=
    (((Tl_integrable c h hh a s ha n hn l).ofReal).const_mul _).integrableOn
  rw [integral_const_mul, integral_finset_sum _ (fun l _ => hI l)]
  have hl (l : ι) : (∫ q in D, (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)))*((Tl c h a s n l q : ℝ) : ℂ))=
      (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)))*((halfDisk (n l) (h l*a) s : ℝ) : ℂ) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_complex_ofReal]
    congr 1
    exact model_pos D (c l) (n l) (h l*a) s (hDs l)
  simp_rw [hl]
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Complex.re_mul_ofReal]

/-- Local-model absolute bypass outside the section `D`, for disjoint dipole disks. -/
theorem model_bypass (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a s : ℝ) (ha : 0<a) (Λ : ℂ)
    (e m : ι → ℂ) (n : ι → Plane) (η0 η1 : ι → ℂ)
    (hη0 : ∀ l, η0 l=-(m l)*((n l 1 : ℝ) : ℂ)) (hη1 : ∀ l, η1 l=m l*((n l 0 : ℝ) : ℂ))
    (hn : ∀ l, ‖n l‖=1) (hsep : ∀ l k, l≠k → 2*s<‖c l-c k‖) (D : Set Plane)
    (hDs : ∀ l, D ∩ closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s)) :
    OQ14.RestrictedTEPassageTransfer.bypass volume D (modelFn c h ρ a s Λ e η0 η1)=
      a*∑ l, ‖((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)‖*halfDisk (n l) (h l*a) s := by
  unfold OQ14.RestrictedTEPassageTransfer.bypass
  have hnorm : ∀ q, ‖modelFn c h ρ a s Λ e η0 η1 q‖=
      a*∑ l, ‖((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)‖*‖Tl c h a s n l q‖ := by
    intro q
    rw [model_eq c h hh ρ a s ha Λ e m n η0 η1 hη0 hη1 q, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    congr 1
    rw [norm_sum_disjoint]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [norm_mul, norm_neg, Complex.norm_real]
    · intro l k hlk
      by_contra hcon
      push_neg at hcon
      have hl : q∈closedBall (c l) s := by
        by_contra hq
        apply hcon.1
        unfold Tl
        rw [Set.indicator_of_not_mem hq]
        simp
      have hk : q∈closedBall (c k) s := by
        by_contra hq
        apply hcon.2
        unfold Tl
        rw [Set.indicator_of_not_mem hq]
        simp
      have h1 : ‖c l-c k‖≤‖q-c l‖+‖q-c k‖ := by
        calc ‖c l-c k‖=‖(q-c k)-(q-c l)‖ := by congr 1; abel
          _ ≤ ‖q-c k‖+‖q-c l‖ := by
            have := norm_sub_le (q-c k) (q-c l)
            linarith
          _ = ‖q-c l‖+‖q-c k‖ := add_comm _ _
      have h2 : ‖q-c l‖≤s := by simpa only [mem_closedBall, dist_eq_norm] using hl
      have h3 : ‖q-c k‖≤s := by simpa only [mem_closedBall, dist_eq_norm] using hk
      have := hsep l k hlk
      linarith
  simp_rw [hnorm]
  have hI (l : ι) : IntegrableOn (fun q => ‖((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)‖*‖Tl c h a s n l q‖) Dᶜ :=
    (((Tl_integrable c h hh a s ha n hn l).norm).const_mul _).integrableOn
  rw [integral_const_mul, integral_finset_sum _ (fun l _ => hI l)]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [integral_const_mul]
  congr 1
  exact model_neg D (c l) (n l) (h l*a) s (mul_pos (hh l) ha) (hDs l)

end OQ14.RestrictedTEDipoleConcentration
#print axioms OQ14.RestrictedTEDipoleConcentration.vol_ball
#print axioms OQ14.RestrictedTEDipoleConcentration.cross_two
#print axioms OQ14.RestrictedTEDipoleConcentration.flux_decomp
#print axioms OQ14.RestrictedTEDipoleConcentration.fluxFn_sub_model
#print axioms OQ14.RestrictedTEDipoleConcentration.above_normal
#print axioms OQ14.RestrictedTEDipoleConcentration.diff_ne
#print axioms OQ14.RestrictedTEDipoleConcentration.hess_bound
#print axioms OQ14.RestrictedTEDipoleConcentration.hess_integrable_mass
#print axioms OQ14.RestrictedTEDipoleConcentration.bound_cross
#print axioms OQ14.RestrictedTEDipoleConcentration.bound_diff
#print axioms OQ14.RestrictedTEDipoleConcentration.bound_outside
#print axioms OQ14.RestrictedTEDipoleConcentration.profile_eq
#print axioms OQ14.RestrictedTEDipoleConcentration.profile_nonneg
#print axioms OQ14.RestrictedTEDipoleConcentration.corr_le
#print axioms OQ14.RestrictedTEDipoleConcentration.main_le
#print axioms OQ14.RestrictedTEDipoleConcentration.g1_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.g2_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.profile_translate_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.g3_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.g1_integral_le
#print axioms OQ14.RestrictedTEDipoleConcentration.g2_integral_le
#print axioms OQ14.RestrictedTEDipoleConcentration.g3_integral
#print axioms OQ14.RestrictedTEDipoleConcentration.concentration_bound
#print axioms OQ14.RestrictedTEDipoleConcentration.ip_apply
#print axioms OQ14.RestrictedTEDipoleConcentration.term_eq
#print axioms OQ14.RestrictedTEDipoleConcentration.norm_sum_disjoint
#print axioms OQ14.RestrictedTEDipoleConcentration.psi_translate_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.Tl_integrable
#print axioms OQ14.RestrictedTEDipoleConcentration.model_eq
#print axioms OQ14.RestrictedTEDipoleConcentration.model_passage
#print axioms OQ14.RestrictedTEDipoleConcentration.model_bypass
