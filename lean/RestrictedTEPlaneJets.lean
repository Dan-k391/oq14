import RestrictedTEUnitSphere
import RestrictedTEDipoleConcentration
import RestrictedTEPassageTransfer

/-! Application of the dipole concentration estimate to the actual explicit parity device: ball-centre field
values are replaced by plane jets with an explicit error, and the local passage and absolute bypass are
transferred to the exact finite-dipole flux and then to the actual complete flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPlaneJets
open Complex MeasureTheory Metric Set Filter Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
open OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem electric_continuous (A : Index →₀ ℂ) (i : Fin 3) : Continuous (fun x => electric A x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (DebyeCalculus.toroidal_smooth _ x (RestrictedTEFields.potential_smooth 1 A).contDiffAt i).continuousAt

theorem electric_sum_apply (cf : κ → ℂ) (A : κ → Index →₀ ℂ) (x : Space) (j : Fin 3) :
    electric (∑ k, cf k • A k) x j=∑ k, cf k*electric (A k) x j := by
  rw [← OQ14.RestrictedTEFieldLinear.electricMap_apply]
  simp only [map_sum, map_smul, OQ14.RestrictedTEFieldLinear.electricMap_apply]
  simp [Finset.sum_apply]

theorem magnetic_sum_apply (cf : κ → ℂ) (A : κ → Index →₀ ℂ) (x : Space) (j : Fin 3) :
    magnetic (∑ k, cf k • A k) x j=∑ k, cf k*magnetic (A k) x j := by
  rw [← OQ14.RestrictedTEFieldLinear.magneticMap_apply]
  simp only [map_sum, map_smul, OQ14.RestrictedTEFieldLinear.magneticMap_apply]
  simp [Finset.sum_apply]

theorem magnetic_smul_apply (z : ℂ) (A : Index →₀ ℂ) (x : Space) (j : Fin 3) :
    magnetic (z • A) x j=z*magnetic A x j := by
  rw [RestrictedTEScale.magnetic_smul]
  rfl

theorem electric_smul_apply (z : ℂ) (A : Index →₀ ℂ) (x : Space) (j : Fin 3) :
    electric (z • A) x j=z*electric A x j := by
  rw [RestrictedTEScale.electric_smul]
  rfl

/-- The polarization factor `3χ/(χ+3)` as a complex number. -/
def lam (χ : ℝ) : ℂ := ((3*χ/(χ+3) : ℝ) : ℂ)

theorem dipoleFlux_eq_fluxFn (c : ι → Plane) (h : ι → ℝ) (p : ℝ → ι → Space)
    (hp : ∀ a l, p a l=abovePoint (c l) (h l*a)) (ρ χ a : ℝ) (A' : Index →₀ ℂ) (q : Plane) :
    RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
      ((a : ℂ)⁻¹ • A') q=
    fluxFn c h ρ a (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
      (fun x j => (a : ℂ)⁻¹*magnetic A' x j) q := by
  unfold RestrictedTEDipoleError.dipoleFlux fluxFn
  have hpa : p a=centre c h a := funext fun l => hp a l
  rw [hpa]
  have hc : conjugate (magnetic ((a : ℂ)⁻¹ • A') (MaxwellPlaneTail.planePoint q))=
      fun j => conj ((a : ℂ)⁻¹*magnetic A' (MaxwellPlaneTail.planePoint q) j) := by
    funext j
    simp only [conjugate, magnetic_smul_apply]
  rw [hc]

theorem polarization_apply (χ : ℝ) (E : Fin 3 → ℂ) (j : Fin 3) :
    (StaticSpherePolarization.polarization χ E) j=lam χ*E j := by
  simp [StaticSpherePolarization.polarization, lam]

theorem hP_actual (c : ι → Plane) (h : ι → ℝ) (p : ℝ → ι → Space)
    (hp : ∀ a l, p a l=abovePoint (c l) (h l*a)) (χ a : ℝ) (A' : Index →₀ ℂ) (l : ι) (j : Fin 3) :
    (StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l))) j=
      lam χ*((a : ℂ)⁻¹)*((if j=2 then electric A' (MaxwellPlaneTail.planePoint (c l)) 2 else 0)+
        (electric A' (centre c h a l) j-electric A' (MaxwellPlaneTail.planePoint (c l)) j)) := by
  rw [polarization_apply, electric_smul_apply, hp a l]
  by_cases hj : j=2
  · subst hj
    simp only [if_true]
    unfold centre
    ring
  · rw [if_neg hj, electric_tangent_zero A' (c l) j hj]
    unfold centre
    ring


/-- Sum of the electric jets of the family at the plane point of the dipole `l` (a bound for the jet). -/
def Ehat (A : κ → Index →₀ ℂ) (c : ι → Plane) (l : ι) : ℝ :=
  ∑ k, ‖electric (A k) (MaxwellPlaneTail.planePoint (c l)) 2‖

/-- The continuity modulus of the electric fields of the family between the dipole centres and the plane jets. -/
def wδ (A : κ → Index →₀ ℂ) (c : ι → Plane) (h : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ k, ∑ l, ∑ j : Fin 3, ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖

theorem continuous_above (c : Plane) : Continuous (fun t : ℝ => abovePoint c t) := by
  unfold abovePoint
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  fin_cases i
  · simp [continuous_const]
  · simp [continuous_const]
  · simpa using continuous_id

theorem exists_M (A : κ → Index →₀ ℂ) :
    ∃ M : ℝ, 0≤M ∧ ∀ cf : κ → ℂ, (∀ k, ‖cf k‖≤1) → ∀ x j, ‖magnetic (∑ k, cf k • A k) x j‖≤M := by
  have hb : ∀ k, ∃ B : ℝ, 0≤B ∧ ∀ x j, ‖magnetic (A k) x j‖≤B := fun k =>
    RestrictedTEMagnetic.magnetic_bounded (A k)
  choose B hB0 hB using hb
  refine ⟨∑ k, B k, Finset.sum_nonneg fun k _ => hB0 k, ?_⟩
  intro cf hcf x j
  rw [magnetic_sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  calc ‖cf k‖*‖magnetic (A k) x j‖≤1*B k := mul_le_mul (hcf k) (hB k x j) (norm_nonneg _) zero_le_one
    _ = B k := one_mul _

theorem tendsto_wδ (A : κ → Index →₀ ℂ) (c : ι → Plane) (h : ι → ℝ) :
    Tendsto (wδ A c h) (𝓝[>] 0) (𝓝 0) := by
  unfold wδ
  have hterm (k : κ) (l : ι) (j : Fin 3) : Tendsto (fun a : ℝ =>
      ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖)
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => electric (A k) (abovePoint (c l) (h l*a)) j) :=
      (electric_continuous (A k) j).comp ((continuous_above (c l)).comp (continuous_const.mul continuous_id))
    have h0 : abovePoint (c l) (h l*0)=MaxwellPlaneTail.planePoint (c l) := by
      simp [abovePoint, MaxwellPlaneTail.planePoint]
    have := ((hcont.sub (continuous_const : Continuous fun _ : ℝ =>
      electric (A k) (MaxwellPlaneTail.planePoint (c l)) j)).norm).tendsto 0
    simp only [h0, sub_self, norm_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := tendsto_finset_sum Finset.univ (fun k _ => tendsto_finset_sum Finset.univ
    (fun l _ => tendsto_finset_sum Finset.univ (fun j _ => hterm k l j)))
  simpa using this

theorem eventually_cont (c : ι → Plane) (A : κ → Index →₀ ℂ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (k : κ) (l : ι) (j : Fin 3) (q : Plane), q∈closedBall (c l) s →
      ‖magnetic (A k) (MaxwellPlaneTail.planePoint q) j-
        magnetic (A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤ε := by
  refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun j => ?_
  have hc : ContinuousAt (fun q : Plane => magnetic (A k) (MaxwellPlaneTail.planePoint q) j) (c l) :=
    ((RestrictedTEMagnetic.magnetic_continuous (A k) j).comp
      MaxwellPlaneTail.planePoint_continuous).continuousAt
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc ε hε
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hδ)] with s hs q hq
  have hq' : dist q (c l)<δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hq) hs
  have := hd hq'
  rw [dist_eq_norm] at this
  exact this.le


theorem delta_bound (A : κ → Index →₀ ℂ) (c : ι → Plane) (h : ι → ℝ) (a : ℝ) (cf : κ → ℂ)
    (hcf : ∀ k, ‖cf k‖≤1) (l : ι) (j : Fin 3) :
    ‖electric (∑ k, cf k • A k) (centre c h a l) j-
      electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤wδ A c h a := by
  rw [electric_sum_apply, electric_sum_apply, ← Finset.sum_sub_distrib]
  have hterm : ∀ k, ‖cf k*electric (A k) (centre c h a l) j-cf k*electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤
      ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖ := by
    intro k
    rw [← mul_sub, norm_mul]
    calc ‖cf k‖*_≤1*_ := mul_le_mul_of_nonneg_right (hcf k) (norm_nonneg _)
      _ = _ := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hterm k).trans ?_)
  unfold wδ
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : (‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖)≤
      ∑ j : Fin 3, ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖ :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖electric (A k) (centre c h a l) j-
      electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j : Fin 3, ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖)≤
      ∑ l : ι, ∑ j : Fin 3, ‖electric (A k) (centre c h a l) j-electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖ :=
    Finset.single_le_sum (f := fun l : ι => ∑ j : Fin 3, ‖electric (A k) (centre c h a l) j-
      electric (A k) (MaxwellPlaneTail.planePoint (c l)) j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ l)
  exact h1.trans h2

theorem jet_bound (A : κ → Index →₀ ℂ) (c : ι → Plane) (s ε : ℝ) (cf : κ → ℂ) (hcf : ∀ k, ‖cf k‖≤1)
    (hε : ∀ (k : κ) (l : ι) (j : Fin 3) (q : Plane), q∈closedBall (c l) s →
      ‖magnetic (A k) (MaxwellPlaneTail.planePoint q) j-
        magnetic (A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤ε)
    (l : ι) (q : Plane) (hq : q∈closedBall (c l) s) (j : Fin 3) :
    ‖magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint q) j-
      magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤(Fintype.card κ : ℝ)*ε := by
  rw [magnetic_sum_apply, magnetic_sum_apply, ← Finset.sum_sub_distrib]
  have hterm : ∀ k, ‖cf k*magnetic (A k) (MaxwellPlaneTail.planePoint q) j-
      cf k*magnetic (A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤ε := by
    intro k
    rw [← mul_sub, norm_mul]
    have h0 : 0≤ε := (norm_nonneg _).trans (hε k l j q hq)
    calc ‖cf k‖*_≤1*ε := mul_le_mul (hcf k) (hε k l j q hq) (norm_nonneg _) zero_le_one
      _ = ε := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hterm k).trans ?_)
  simp

theorem e_bound (A : κ → Index →₀ ℂ) (c : ι → Plane) (cf : κ → ℂ) (hcf : ∀ k, ‖cf k‖≤1) (l : ι) :
    ‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖≤Ehat A c l := by
  rw [electric_sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  calc ‖cf k‖*_≤1*_ := mul_le_mul_of_nonneg_right (hcf k) (norm_nonneg _)
    _ = _ := one_mul _


theorem div_sqrt_aux (a X d : ℝ) (ha : 0<a) : a*X*d/Real.sqrt a=Real.sqrt a*X*d := by
  have hs := Real.sqrt_pos.mpr ha
  have hq := Real.mul_self_sqrt ha.le
  rw [div_eq_iff hs.ne']
  calc a*X*d=(Real.sqrt a*Real.sqrt a)*X*d := by rw [hq]
    _ = Real.sqrt a*X*d*Real.sqrt a := by ring

theorem sqrt_tendsto : Tendsto (fun a : ℝ => Real.sqrt a) (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨(Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).mono_left nhdsWithin_le_nhds,
    Filter.eventually_of_mem self_mem_nhdsWithin (fun _ ha => Real.sqrt_pos.mpr ha)⟩

/-- Uniform (over the unit polydisc of coefficients) L1 concentration of the actual finite-dipole flux onto the
local jet model with cut-off radius `√a`. -/
theorem concentration_uniform (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (p : ℝ → ι → Space)
    (hp : ∀ a l, p a l=abovePoint (c l) (h l*a)) (ρ χ : ℝ) (hρ : 0≤ρ) (A : κ → Index →₀ ℂ)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ cf : κ → ℂ, (∀ k, ‖cf k‖≤1) →
      (∫ q : Plane, ‖RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • ∑ k, cf k • A k) (p a l)))
        ((a : ℂ)⁻¹ • ∑ k, cf k • A k) q-
        modelFn c h ρ a (Real.sqrt a) (lam χ)
          (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1) q‖)≤ε := by
  obtain ⟨M, hM0, hM⟩ := exists_M A
  have hVb : 0≤Vb ρ := by unfold Vb; positivity
  let K : ℝ := Vb ρ*‖lam χ‖
  have hK : 0≤K := mul_nonneg hVb (norm_nonneg _)
  let dc := PlaneInverseCube.diskConstant
  have hEh : ∀ l, 0≤Ehat A c l := fun l => Finset.sum_nonneg fun k _ => norm_nonneg _
  let S1 : ℝ := K*∑ l, 6*Ehat A c l*(Fintype.card κ : ℝ)/h l
  have hS1 : 0≤S1 := mul_nonneg hK (Finset.sum_nonneg fun l _ => by
    have := hEh l; have := hh l; positivity)
  let ε1 : ℝ := ε/(3*(S1+1))
  have hε1 : 0<ε1 := by positivity
  have F1 : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ (k : κ) (l : ι) (j : Fin 3) (q : Plane), q∈closedBall (c l) (Real.sqrt a) →
      ‖magnetic (A k) (MaxwellPlaneTail.planePoint q) j-
        magnetic (A k) (MaxwellPlaneTail.planePoint (c l)) j‖≤ε1 :=
    sqrt_tendsto.eventually (eventually_cont c A ε1 hε1)
  have F2 : ∀ᶠ a : ℝ in 𝓝[>] 0, K*∑ l, 18*M*wδ A c h a/h l≤ε/3 := by
    have ht := (tendsto_finset_sum (Finset.univ : Finset ι) (fun l _ =>
      (((tendsto_wδ A c h).const_mul (18*M)).div_const (h l)))).const_mul K
    simp only [mul_zero, zero_div, Finset.sum_const_zero] at ht
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<ε/3))).mono fun a ha => ha.le
  have F3 : ∀ᶠ a : ℝ in 𝓝[>] 0, K*∑ l, Real.sqrt a*(2*Ehat A c l*M/Real.pi)*dc≤ε/3 := by
    have hs : Tendsto (fun a : ℝ => Real.sqrt a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ)≤𝓝 0))
    have ht := (tendsto_finset_sum (Finset.univ : Finset ι) (fun l _ =>
      ((hs.mul_const (2*Ehat A c l*M/Real.pi)).mul_const dc))).const_mul K
    simp only [zero_mul, Finset.sum_const_zero, mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<ε/3))).mono fun a ha => ha.le
  filter_upwards [F1, F2, F3, self_mem_nhdsWithin] with a h1 h2 h3 ha
  change 0<a at ha
  intro cf hcf
  have hsa : 0<Real.sqrt a := Real.sqrt_pos.mpr ha
  have heq : ∀ q : Plane, RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • ∑ k, cf k • A k) (p a l)))
      ((a : ℂ)⁻¹ • ∑ k, cf k • A k) q=
      fluxFn c h ρ a (fun l => StaticSpherePolarization.polarization χ
        (electric ((a : ℂ)⁻¹ • ∑ k, cf k • A k) (p a l)))
        (fun x j => (a : ℂ)⁻¹*magnetic (∑ k, cf k • A k) x j) q :=
    fun q => dipoleFlux_eq_fluxFn c h p hp ρ χ a _ q
  simp only [heq]
  have hωδ : 0≤wδ A c h a := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    Finset.sum_nonneg fun j _ => norm_nonneg _
  have hωH : 0≤(Fintype.card κ : ℝ)*ε1 := by positivity
  have hmain := concentration_bound c h hh ρ a (Real.sqrt a) hρ ha hsa (lam χ)
    (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l j => electric (∑ k, cf k • A k) (centre c h a l) j-
      electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) j)
    (fun l => StaticSpherePolarization.polarization χ
      (electric ((a : ℂ)⁻¹ • ∑ k, cf k • A k) (p a l)))
    (magnetic (∑ k, cf k • A k))
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1)
    M (wδ A c h a) ((Fintype.card κ : ℝ)*ε1) hωδ hωH
    (fun l j => hP_actual c h p hp χ a (∑ k, cf k • A k) l j) (hM cf hcf)
    (fun l j => delta_bound A c h a cf hcf l j)
    (fun l q hq => ⟨jet_bound A c (Real.sqrt a) ε1 cf hcf h1 l q hq 0,
      jet_bound A c (Real.sqrt a) ε1 cf hcf h1 l q hq 1⟩)
  refine hmain.trans ?_
  have hterm : ∀ l, ((18*M*wδ A c h a+6*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ((Fintype.card κ : ℝ)*ε1))/h l+a*(2*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*M/Real.pi)*dc/
        Real.sqrt a)≤18*M*wδ A c h a/h l+6*Ehat A c l*(Fintype.card κ : ℝ)/h l*ε1+
          Real.sqrt a*(2*Ehat A c l*M/Real.pi)*dc := by
    intro l
    have hl := hh l
    have he := e_bound A c cf hcf l
    have hdc : 0≤dc := by
      simp [dc, PlaneInverseCube.diskConstant]
    have hpi := Real.pi_pos
    have hdiv : a/Real.sqrt a=Real.sqrt a := Real.div_sqrt
    have e1 : a*(2*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*M/Real.pi)*dc/Real.sqrt a=
        Real.sqrt a*(2*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*M/Real.pi)*dc :=
      div_sqrt_aux a _ dc ha
    rw [e1]
    have e2 : 6*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ((Fintype.card κ : ℝ)*ε1)/h l≤6*Ehat A c l*(Fintype.card κ : ℝ)/h l*ε1 := by
      have : 6*Ehat A c l*(Fintype.card κ : ℝ)/h l*ε1=6*Ehat A c l*((Fintype.card κ : ℝ)*ε1)/h l := by ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hl.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hωH
    have e3 : Real.sqrt a*(2*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*M/Real.pi)*dc≤
        Real.sqrt a*(2*Ehat A c l*M/Real.pi)*dc := by
      apply mul_le_mul_of_nonneg_right _ hdc
      apply mul_le_mul_of_nonneg_left _ hsa.le
      apply div_le_div_of_nonneg_right _ hpi.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hM0
    have e4 : (18*M*wδ A c h a+6*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ((Fintype.card κ : ℝ)*ε1))/h l=18*M*wδ A c h a/h l+
        6*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*((Fintype.card κ : ℝ)*ε1)/h l := by
      rw [add_div]
    rw [e4]
    linarith
  have hsum := Finset.sum_le_sum (fun l (_ : l∈(Finset.univ : Finset ι)) => hterm l)
  have hK' : Vb ρ*‖lam χ‖*∑ l, ((18*M*wδ A c h a+6*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ((Fintype.card κ : ℝ)*ε1))/h l+a*(2*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*M/Real.pi)*dc/
        Real.sqrt a)≤K*(∑ l, (18*M*wδ A c h a/h l+6*Ehat A c l*(Fintype.card κ : ℝ)/h l*ε1+
          Real.sqrt a*(2*Ehat A c l*M/Real.pi)*dc)) :=
    mul_le_mul_of_nonneg_left hsum hK
  refine hK'.trans ?_
  simp only [Finset.sum_add_distrib, mul_add]
  have hS : K*∑ l, 6*Ehat A c l*(Fintype.card κ : ℝ)/h l*ε1=S1*ε1 := by
    simp only [S1, ← Finset.sum_mul, mul_assoc]
  rw [hS]
  have hS1ε : S1*ε1≤ε/3 := by
    simp only [ε1]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hS1, hε]
  linarith


theorem power_comb (A : κ → Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) (cf : κ → ℂ) :
    RestrictedTEIncoming.physicalPower (∑ k, cf k • A k)=∑ k, ‖cf k‖^2 := by
  rw [← RestrictedTEInput.input_norm_sq]
  have hin : RestrictedTEInput.input (∑ k, cf k • A k)=∑ k, cf k • RestrictedTEInput.input (A k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => map_smul _ _ _)
  rw [hin]
  generalize hv : ∑ k, cf k • RestrictedTEInput.input (A k)=v
  have this : @inner ℂ _ _ v v=∑ j, (starRingEnd ℂ) (cf j)*cf j := by
    rw [← hv]
    exact horth.inner_sum cf cf Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [Complex.conj_mul'] at this
  have h3 : ((‖v‖^2 : ℝ) : ℂ)=((∑ j, ‖cf j‖^2 : ℝ) : ℂ) := by
    push_cast
    exact this
  exact Complex.ofReal_injective h3

theorem int_mul_conj (g : Plane → ℂ) (hg : Integrable g) (H : Plane → ℂ) (hH : Continuous H) (M : ℝ)
    (hb : ∀ q, ‖H q‖≤M) : Integrable (fun q => g q*conj (H q)) := by
  have hf : AEStronglyMeasurable (fun q => conj (H q)) volume :=
    (Complex.continuous_conj.comp hH).aestronglyMeasurable
  have := hg.bdd_mul' hf (Filter.Eventually.of_forall (fun q => by
    rw [RCLike.norm_conj]
    exact hb q))
  exact this.congr (Filter.Eventually.of_forall (fun q => mul_comm _ _))

theorem hess_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (a : ℝ) (ha : 0<a) (l : ι)
    (i j : Fin 3) : Integrable (fun q => hess c h a l q i j) := by
  have hpos : 0<h l*a := mul_pos (hh l) ha
  have hy : h l*a≤|(centre c h a l) 2| := by
    unfold centre
    rw [above_normal, abs_of_pos hpos]
  exact StaticPlaneKernel.plane_kernel_integrable _ hpos _ hy i j

theorem fluxFn_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a : ℝ) (ha : 0<a) (hρ : 0≤ρ)
    (Λ : ℂ) (e : ι → ℂ) (δ : ι → Fin 3 → ℂ) (P : ι → Vec) (H0 : Space → Fin 3 → ℂ)
    (hP : ∀ l j, P l j=Λ*((a : ℂ)⁻¹)*((if j=2 then e l else 0)+δ l j))
    (hHc : ∀ j, Continuous (fun x => H0 x j)) (M : ℝ) (hM : ∀ x j, ‖H0 x j‖≤M) :
    Integrable (fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j)) := by
  have hHq (j : Fin 3) : Continuous (fun q : Plane => H0 (MaxwellPlaneTail.planePoint q) j) :=
    (hHc j).comp MaxwellPlaneTail.planePoint_continuous
  have hmain (l : ι) : Integrable (mainPart c h a e H0 l) := by
    unfold mainPart
    have h1 := int_mul_conj _ (hess_integrable c h hh a ha l 0 2) _ (hHq 1) M (fun q => hM _ 1)
    have h2 := int_mul_conj _ (hess_integrable c h hh a ha l 1 2) _ (hHq 0) M (fun q => hM _ 0)
    exact (h1.sub h2).const_mul (e l)
  have hcorr (l : ι) : Integrable (corrPart c h a δ H0 l) := by
    unfold corrPart
    refine integrable_finset_sum _ (fun j _ => ?_)
    have h1 := int_mul_conj _ (hess_integrable c h hh a ha l 0 j) _ (hHq 1) M (fun q => hM _ 1)
    have h2 := int_mul_conj _ (hess_integrable c h hh a ha l 1 j) _ (hHq 0) M (fun q => hM _ 0)
    exact (h1.sub h2).const_mul (δ l j)
  have hfun : fluxFn c h ρ a P (fun x j => (a : ℂ)⁻¹*H0 x j)=
      fun q => ((Vb ρ*a : ℝ) : ℂ)*Λ*∑ l, (mainPart c h a e H0 l q+corrPart c h a δ H0 l q) :=
    funext fun q => flux_decomp c h ρ a ha hρ Λ e δ P H0 hP q
  rw [hfun]
  exact (integrable_finset_sum _ (fun l _ => (hmain l).add (hcorr l))).const_mul _


theorem Gflux_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (p : ℝ → ι → Space)
    (hp : ∀ a l, p a l=abovePoint (c l) (h l*a)) (ρ χ : ℝ) (hρ : 0≤ρ) (A' : Index →₀ ℂ) (a : ℝ)
    (ha : 0<a) :
    Integrable (fun q : Plane => RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
      ((a : ℂ)⁻¹ • A') q) := by
  obtain ⟨M, hM0, hM⟩ := RestrictedTEMagnetic.magnetic_bounded A'
  have hfun : (fun q : Plane => RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
      ((a : ℂ)⁻¹ • A') q)=
      fluxFn c h ρ a (fun l => StaticSpherePolarization.polarization χ
        (electric ((a : ℂ)⁻¹ • A') (p a l))) (fun x j => (a : ℂ)⁻¹*magnetic A' x j) :=
    funext fun q => dipoleFlux_eq_fluxFn c h p hp ρ χ a A' q
  rw [hfun]
  exact fluxFn_integrable c h hh ρ a ha hρ (lam χ) (fun l => electric A' (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l j => electric A' (centre c h a l) j-electric A' (MaxwellPlaneTail.planePoint (c l)) j)
    (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
    (magnetic A') (fun l j => hP_actual c h p hp χ a A' l j)
    (fun j => RestrictedTEMagnetic.magnetic_continuous A' j) M hM

/-- The tangential magnetic jet coefficient of the dipole `l` along the tangent `(-n₁, n₀)`. -/
def mj (A' : Index →₀ ℂ) (c : ι → Plane) (n : ι → Plane) (l : ι) : ℂ :=
  magnetic A' (MaxwellPlaneTail.planePoint (c l)) 1*((n l 0 : ℝ) : ℂ)-
    magnetic A' (MaxwellPlaneTail.planePoint (c l)) 0*((n l 1 : ℝ) : ℂ)

/-- The local passage coefficient of the dipole `l`. -/
def kap (ρ χ : ℝ) (A' : Index →₀ ℂ) (c : ι → Plane) (n : ι → Plane) (l : ι) : ℂ :=
  -(((Vb ρ : ℝ) : ℂ)*lam χ*electric A' (MaxwellPlaneTail.planePoint (c l)) 2*conj (mj A' c n l))

theorem kap_bound (A : κ → Index →₀ ℂ) (c : ι → Plane) (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (ρ χ : ℝ)
    (hρ : 0≤ρ) (M : ℝ) (cf : κ → ℂ) (hcf : ∀ k, ‖cf k‖≤1)
    (hM : ∀ x j, ‖magnetic (∑ k, cf k • A k) x j‖≤M) (l : ι) :
    ‖kap ρ χ (∑ k, cf k • A k) c n l‖≤Vb ρ*‖lam χ‖*Ehat A c l*(2*M) := by
  have hVb : 0≤Vb ρ := by unfold Vb; positivity
  have hn0 : ‖(n l 0 : ℝ)‖≤1 := by
    have := PiLp.norm_apply_le (n l) 0
    rwa [hn l] at this
  have hn1 : ‖(n l 1 : ℝ)‖≤1 := by
    have := PiLp.norm_apply_le (n l) 1
    rwa [hn l] at this
  have hmj : ‖mj (∑ k, cf k • A k) c n l‖≤2*M := by
    unfold mj
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have h1 := hM (MaxwellPlaneTail.planePoint (c l)) 1
    have h0 := hM (MaxwellPlaneTail.planePoint (c l)) 0
    have hM0 : 0≤M := (norm_nonneg _).trans h1
    nlinarith [mul_le_mul h1 hn0 (norm_nonneg _) hM0, mul_le_mul h0 hn1 (norm_nonneg _) hM0,
      norm_nonneg (magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1)]
  have he := e_bound A c cf hcf l
  unfold kap
  rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hVb,
    RCLike.norm_conj]
  have hM0 : 0≤2*M := (norm_nonneg _).trans hmj
  have hE : 0≤Ehat A c l := (norm_nonneg _).trans he
  have h1 : ‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
      ‖mj (∑ k, cf k • A k) c n l‖≤Ehat A c l*(2*M) :=
    mul_le_mul he hmj (norm_nonneg _) hE
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hVb (norm_nonneg (lam χ)))
  calc Vb ρ*‖lam χ‖*‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ‖mj (∑ k, cf k • A k) c n l‖
      =(Vb ρ*‖lam χ‖)*(‖electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2‖*
        ‖mj (∑ k, cf k • A k) c n l‖) := by ring
    _ ≤ (Vb ρ*‖lam χ‖)*(Ehat A c l*(2*M)) := h2
    _ = Vb ρ*‖lam χ‖*Ehat A c l*(2*M) := by ring

theorem sqrt_div_tendsto : Tendsto (fun a : ℝ => Real.sqrt a/a) (𝓝[>] 0) atTop := by
  have hev : ∀ᶠ a : ℝ in 𝓝[>] 0, (Real.sqrt a)⁻¹=Real.sqrt a/a := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [Real.sqrt_div_self', one_div]
  exact (tendsto_inv_nhdsGT_zero.comp sqrt_tendsto).congr' hev

theorem theta_tendsto (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (h : ι → ℝ) (hh : ∀ l, 0<h l) (w : ι → ℝ) :
    Tendsto (fun a : ℝ => ∑ l, w l*|a*halfDisk (n l) (h l*a) (Real.sqrt a)-halfPlane (n l) (h l)|)
      (𝓝[>] 0) (𝓝 0) := by
  have hl (l : ι) : Tendsto (fun a : ℝ => w l*|a*halfDisk (n l) (h l*a) (Real.sqrt a)-halfPlane (n l) (h l)|)
      (𝓝[>] 0) (𝓝 0) := by
    have := (scaled_limit (n l) (hn l) (h l) (hh l) (fun a => Real.sqrt a) sqrt_div_tendsto)
    have h2 := (this.sub_const (halfPlane (n l) (h l))).abs.const_mul (w l)
    simpa using h2
  simpa using tendsto_finset_sum Finset.univ (fun l _ => hl l)


/-- Regime of small `a` in which the geometry is that of the local model. -/
theorem regime (c : ι → Plane) (hcd : ∀ l k, l≠k → c l≠c k) (n : ι → Plane) (D : Set Plane)
    (hD : ∀ l, ∃ s0 : ℝ, 0<s0 ∧ ∀ s : ℝ, 0<s → s≤s0 →
      D ∩ closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s)) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, 0<a ∧ (∀ l k, l≠k → 2*Real.sqrt a<‖c l-c k‖) ∧
      (∀ l, D ∩ closedBall (c l) (Real.sqrt a)=
        (fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 (Real.sqrt a))) := by
  have E1 : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ l k, l≠k → 2*s<‖c l-c k‖ := by
    refine Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun k => ?_
    by_cases hlk : l=k
    · exact Filter.Eventually.of_forall (fun s hne => absurd hlk hne)
    · have hd : 0<‖c l-c k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcd l k hlk))
      filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds (half_pos hd))] with s hs _
      linarith
  have E2 : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ l, D ∩ closedBall (c l) s=
      (fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s) := by
    refine Filter.eventually_all.2 fun l => ?_
    obtain ⟨s0, hs0, hs⟩ := hD l
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hs0)] with s hs1 hs2
    exact hs s hs1 hs2.le
  filter_upwards [self_mem_nhdsWithin, sqrt_tendsto.eventually E1, sqrt_tendsto.eventually E2] with a ha h1 h2
  exact ⟨ha, h1, h2⟩

theorem abs_sum_sub_le {ι : Type*} [Fintype ι] (r d f w : ι → ℝ) (hr : ∀ l, |r l|≤w l) :
    |(∑ l, r l*d l)-∑ l, r l*f l|≤∑ l, w l*|d l-f l| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hr l) (abs_nonneg _)

theorem model_close (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ χ : ℝ) (hρ : 0≤ρ)
    (A : κ → Index →₀ ℂ) (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (D : Set Plane)
    (hcd : ∀ l k, l≠k → c l≠c k)
    (hD : ∀ l, ∃ s0 : ℝ, 0<s0 ∧ ∀ s : ℝ, 0<s → s≤s0 →
      D ∩ closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s))
    (p0 ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ cf : κ → ℂ, (∀ k, ‖cf k‖≤1) →
      (∀ l, magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0=
          -(mj (∑ k, cf k • A k) c n l)*((n l 1 : ℝ) : ℂ) ∧
        magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1=
          mj (∑ k, cf k • A k) c n l*((n l 0 : ℝ) : ℂ)) →
      (∀ l, 0≤(kap ρ χ (∑ k, cf k • A k) c n l).re ∧ (kap ρ χ (∑ k, cf k • A k) c n l).im=0) →
      (∑ l, (kap ρ χ (∑ k, cf k • A k) c n l).re*halfPlane (n l) (h l)=p0) →
      |OQ14.RestrictedTEPassageTransfer.passage volume D
        (modelFn c h ρ a (Real.sqrt a) (lam χ)
          (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1))-p0|≤ε ∧
      |OQ14.RestrictedTEPassageTransfer.bypass volume D
        (modelFn c h ρ a (Real.sqrt a) (lam χ)
          (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
          (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1))-p0|≤ε := by
  obtain ⟨M, hM0, hM⟩ := exists_M A
  have hVb : 0≤Vb ρ := by unfold Vb; positivity
  let w : ι → ℝ := fun l => Vb ρ*‖lam χ‖*Ehat A c l*(2*M)
  have hθ := (theta_tendsto n hn h hh w).eventually (gt_mem_nhds hε)
  filter_upwards [regime c hcd n D hD, hθ] with a hreg hθa
  obtain ⟨ha, hsep, hDs⟩ := hreg
  intro cf hcf hT hK hB
  have hη0 : ∀ l, magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0=
      -(mj (∑ k, cf k • A k) c n l)*((n l 1 : ℝ) : ℂ) := fun l => (hT l).1
  have hη1 : ∀ l, magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1=
      mj (∑ k, cf k • A k) c n l*((n l 0 : ℝ) : ℂ) := fun l => (hT l).2
  have hpass := model_passage c h hh ρ a (Real.sqrt a) ha (lam χ)
    (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l => mj (∑ k, cf k • A k) c n l) n
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1) hη0 hη1 hn D hDs
  have hbyp := model_bypass c h hh ρ a (Real.sqrt a) ha (lam χ)
    (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l => mj (∑ k, cf k • A k) c n l) n
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1) hη0 hη1 hn hsep D hDs
  have hkb : ∀ l, |(kap ρ χ (∑ k, cf k • A k) c n l).re|≤w l := fun l =>
    (Complex.abs_re_le_norm _).trans (kap_bound A c n hn ρ χ hρ M cf hcf (hM cf hcf) l)
  have hnorm : ∀ l, ‖((Vb ρ : ℝ) : ℂ)*lam χ*electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2*
      conj (mj (∑ k, cf k • A k) c n l)‖=(kap ρ χ (∑ k, cf k • A k) c n l).re := by
    intro l
    have hk : kap ρ χ (∑ k, cf k • A k) c n l=(((kap ρ χ (∑ k, cf k • A k) c n l).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using (hK l).2)
    have : ‖((Vb ρ : ℝ) : ℂ)*lam χ*electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2*
        conj (mj (∑ k, cf k • A k) c n l)‖=‖kap ρ χ (∑ k, cf k • A k) c n l‖ := by
      unfold kap
      rw [norm_neg]
    rw [this]
    conv_lhs => rw [hk]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK l).1]
  constructor
  · rw [hpass, ← hB, Finset.mul_sum]
    have e1 : (∑ l, a*((-(((Vb ρ : ℝ) : ℂ)*lam χ*electric (∑ k, cf k • A k)
        (MaxwellPlaneTail.planePoint (c l)) 2*conj (mj (∑ k, cf k • A k) c n l))).re*
          halfDisk (n l) (h l*a) (Real.sqrt a)))=
        ∑ l, (kap ρ χ (∑ k, cf k • A k) c n l).re*(a*halfDisk (n l) (h l*a) (Real.sqrt a)) :=
      Finset.sum_congr rfl (fun l _ => by unfold kap; ring)
    rw [e1]
    exact ((abs_sum_sub_le (fun l => (kap ρ χ (∑ k, cf k • A k) c n l).re)
      (fun l => a*halfDisk (n l) (h l*a) (Real.sqrt a)) (fun l => halfPlane (n l) (h l)) w hkb).trans
      hθa.le)
  · rw [hbyp, ← hB, Finset.mul_sum]
    have e1 : (∑ l, a*(‖((Vb ρ : ℝ) : ℂ)*lam χ*electric (∑ k, cf k • A k)
        (MaxwellPlaneTail.planePoint (c l)) 2*conj (mj (∑ k, cf k • A k) c n l)‖*
          halfDisk (n l) (h l*a) (Real.sqrt a)))=
        ∑ l, (kap ρ χ (∑ k, cf k • A k) c n l).re*(a*halfDisk (n l) (h l*a) (Real.sqrt a)) :=
      Finset.sum_congr rfl (fun l _ => by rw [hnorm l]; ring)
    rw [e1]
    exact ((abs_sum_sub_le (fun l => (kap ρ χ (∑ k, cf k • A k) c n l).re)
      (fun l => a*halfDisk (n l) (h l*a) (Real.sqrt a)) (fun l => halfPlane (n l) (h l)) w hkb).trans
      hθa.le)


/-- The literal complete flux density of the actual inverse for the input `A'`. -/
def Fflux (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (a : ℝ) (A' : Index →₀ ℂ) (q : Plane) : ℂ :=
  RestrictedTETotalFlux.totalFlux (b/a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A' a)
    ((a : ℂ)⁻¹ • A') q

/-- The exact finite-dipole flux density of the actual polarizations. -/
def Gflux (p : ℝ → ι → Space) (ρ χ a : ℝ) (A' : Index →₀ ℂ) (q : Plane) : ℂ :=
  RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
    ((a : ℂ)⁻¹ • A') q

theorem model_integrable (c : ι → Plane) (h : ι → ℝ) (hh : ∀ l, 0<h l) (ρ a s : ℝ) (ha : 0<a) (Λ : ℂ)
    (e m : ι → ℂ) (n : ι → Plane) (η0 η1 : ι → ℂ)
    (hη0 : ∀ l, η0 l=-(m l)*((n l 1 : ℝ) : ℂ)) (hη1 : ∀ l, η1 l=m l*((n l 0 : ℝ) : ℂ))
    (hn : ∀ l, ‖n l‖=1) :
    Integrable (modelFn c h ρ a s Λ e η0 η1) := by
  have hfun : modelFn c h ρ a s Λ e η0 η1=fun q => (a : ℂ)*∑ l, (-(((Vb ρ : ℝ) : ℂ)*Λ*e l*conj (m l)))*
      ((Tl c h a s n l q : ℝ) : ℂ) := funext fun q => model_eq c h hh ρ a s ha Λ e m n η0 η1 hη0 hη1 q
  rw [hfun]
  exact (integrable_finset_sum _ (fun l _ =>
    ((Tl_integrable c h hh a s ha n hn l).ofReal).const_mul _)).const_mul _

/-- Counted-channel inequalities for the explicit parity device on the physical-power unit sphere of a
constructed orthonormal input family, under explicit geometric and jet hypotheses. -/
theorem explicit_parity_device_counting (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh' : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|)
    (c : ι → Plane) (h : ι → ℝ) (hhpos : ∀ l, 0<h l) (hp : ∀ a l, p a l=abovePoint (c l) (h l*a))
    (hcd : ∀ l k, l≠k → c l≠c k) (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (D : Set Plane)
    (hD : ∀ l, ∃ s0 : ℝ, 0<s0 ∧ ∀ s : ℝ, 0<s → s≤s0 →
      D ∩ closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ closedBall 0 s))
    (A : κ → Index →₀ ℂ) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (HT : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      magnetic A' (MaxwellPlaneTail.planePoint (c l)) 0=-(mj A' c n l)*((n l 1 : ℝ) : ℂ) ∧
        magnetic A' (MaxwellPlaneTail.planePoint (c l)) 1=mj A' c n l*((n l 0 : ℝ) : ℂ))
    (HK : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      0≤(kap ρ χ A' c n l).re ∧ (kap ρ χ A' c n l).im=0)
    (p0 ηt δt : ℝ)
    (HB : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ∑ l, (kap ρ χ A' c n l).re*halfPlane (n l) (h l)=p0)
    (hη : ηt<p0) (hδt : p0<δt) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ηt≤OQ14.RestrictedTEPassageTransfer.passage volume D (Fflux p ρ χ R b hρ hχ hi a A') ∧
      OQ14.RestrictedTEPassageTransfer.bypass volume D (Fflux p ρ χ R b hρ hχ hi a A')≤δt := by
  let ε : ℝ := min (p0-ηt) (δt-p0)/4
  have hε : 0<ε := by
    have : 0<min (p0-ηt) (δt-p0) := lt_min (by linarith) (by linarith)
    simp only [ε]
    positivity
  have hε1 : 3*ε<p0-ηt := by
    have := min_le_left (p0-ηt) (δt-p0)
    simp only [ε]
    linarith
  have hε2 : 3*ε<δt-p0 := by
    have := min_le_right (p0-ηt) (δt-p0)
    simp only [ε]
    linarith
  have hE1 := RestrictedTEUnitSphere.uniform_physical_unit_ball p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh' A
    horth ε hε
  have hE2 := concentration_uniform c h hhpos p hp ρ χ hρ.le A ε hε
  have hE3 := model_close c h hhpos ρ χ hρ.le A n hn D hcd hD p0 ε hε
  filter_upwards [hE1, hE2, hE3, self_mem_nhdsWithin] with a h1 h2 h3 ha
  change 0<a at ha
  intro A' hA' hpow
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA'
  have hsum : (∑ k, ‖cf k‖^2)=1 := by rw [← power_comb A horth cf]; exact hpow
  have hcf : ∀ k, ‖cf k‖≤1 := by
    intro k
    have h1 : ‖cf k‖^2≤∑ k, ‖cf k‖^2 :=
      Finset.single_le_sum (f := fun k => ‖cf k‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    by_contra hne
    push_neg at hne
    nlinarith [norm_nonneg (cf k)]
  obtain ⟨hint, hmass⟩ := h1 _ hA' hpow.le
  have hG := Gflux_integrable c h hhpos p hp ρ χ hρ.le (∑ k, cf k • A k) a ha
  have hFi : Integrable (Fflux p ρ χ R b hρ hχ hi a (∑ k, cf k • A k)) := by
    have := hint.add hG
    refine this.congr (Filter.Eventually.of_forall (fun q => ?_))
    simp only [Pi.add_apply]
    unfold Fflux
    ring
  have hT := HT _ hA' hpow
  have hmod := model_integrable c h hhpos ρ a (Real.sqrt a) ha (lam χ)
    (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l => mj (∑ k, cf k • A k) c n l) n
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1)
    (fun l => (hT l).1) (fun l => (hT l).2) hn
  obtain ⟨hmp, hmb⟩ := h3 cf hcf hT (HK _ hA' hpow) (HB _ hA' hpow)
  have hc2 := h2 cf hcf
  -- abbreviations
  set Fq := Fflux p ρ χ R b hρ hχ hi a (∑ k, cf k • A k) with hFq
  set Gq := Gflux p ρ χ a (∑ k, cf k • A k) with hGq
  set Mq := modelFn c h ρ a (Real.sqrt a) (lam χ)
    (fun l => electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 2)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 0)
    (fun l => magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (c l)) 1) with hMq
  have hGq' : Integrable Gq := hG
  have a1 := OQ14.RestrictedTEPassageTransfer.abs_passage_sub_le D Fq Gq hFi hGq'
  have a2 := OQ14.RestrictedTEPassageTransfer.abs_passage_sub_le D Gq Mq hGq' hmod
  have b1 := OQ14.RestrictedTEPassageTransfer.abs_bypass_sub_le D Fq Gq hFi hGq'
  have b2 := OQ14.RestrictedTEPassageTransfer.abs_bypass_sub_le D Gq Mq hGq' hmod
  have m1 : (∫ q, ‖Fq q-Gq q‖)≤ε := hmass
  have m2 : (∫ q, ‖Gq q-Mq q‖)≤ε := hc2
  have p1 := (abs_le.mp (a1.trans m1)).1
  have p2 := (abs_le.mp (a2.trans m2)).1
  have p3 := (abs_le.mp hmp).1
  have q1 := (abs_le.mp (b1.trans m1)).2
  have q2 := (abs_le.mp (b2.trans m2)).2
  have q3 := (abs_le.mp hmb).2
  constructor
  · linarith
  · linarith

end OQ14.RestrictedTEPlaneJets
#print axioms OQ14.RestrictedTEPlaneJets.electric_continuous
#print axioms OQ14.RestrictedTEPlaneJets.electric_sum_apply
#print axioms OQ14.RestrictedTEPlaneJets.magnetic_sum_apply
#print axioms OQ14.RestrictedTEPlaneJets.magnetic_smul_apply
#print axioms OQ14.RestrictedTEPlaneJets.electric_smul_apply
#print axioms OQ14.RestrictedTEPlaneJets.dipoleFlux_eq_fluxFn
#print axioms OQ14.RestrictedTEPlaneJets.polarization_apply
#print axioms OQ14.RestrictedTEPlaneJets.hP_actual
#print axioms OQ14.RestrictedTEPlaneJets.continuous_above
#print axioms OQ14.RestrictedTEPlaneJets.exists_M
#print axioms OQ14.RestrictedTEPlaneJets.tendsto_wδ
#print axioms OQ14.RestrictedTEPlaneJets.eventually_cont
#print axioms OQ14.RestrictedTEPlaneJets.delta_bound
#print axioms OQ14.RestrictedTEPlaneJets.jet_bound
#print axioms OQ14.RestrictedTEPlaneJets.e_bound
#print axioms OQ14.RestrictedTEPlaneJets.div_sqrt_aux
#print axioms OQ14.RestrictedTEPlaneJets.sqrt_tendsto
#print axioms OQ14.RestrictedTEPlaneJets.concentration_uniform
#print axioms OQ14.RestrictedTEPlaneJets.power_comb
#print axioms OQ14.RestrictedTEPlaneJets.int_mul_conj
#print axioms OQ14.RestrictedTEPlaneJets.hess_integrable
#print axioms OQ14.RestrictedTEPlaneJets.fluxFn_integrable
#print axioms OQ14.RestrictedTEPlaneJets.Gflux_integrable
#print axioms OQ14.RestrictedTEPlaneJets.kap_bound
#print axioms OQ14.RestrictedTEPlaneJets.sqrt_div_tendsto
#print axioms OQ14.RestrictedTEPlaneJets.theta_tendsto
#print axioms OQ14.RestrictedTEPlaneJets.regime
#print axioms OQ14.RestrictedTEPlaneJets.abs_sum_sub_le
#print axioms OQ14.RestrictedTEPlaneJets.model_close
#print axioms OQ14.RestrictedTEPlaneJets.model_integrable
#print axioms OQ14.RestrictedTEPlaneJets.explicit_parity_device_counting
