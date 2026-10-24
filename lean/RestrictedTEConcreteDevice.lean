import RestrictedTEPlaneJets
import PhysicalTEBandInterpolation

/-! A concrete explicit parity device: `N` small dielectric balls at heights `h a` above the distinct points
`(r, y_l, 0)` of one line, section `D = {x > r}`, and the orthonormal finite physical inputs of the interpolation
theorem with the prescribed plane jets `(E_z, H_x, H_y) = (-1/Λ, 0, 1)` at their own point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEConcreteDevice
open Complex MeasureTheory Metric Set Filter Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
open OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEPlaneJets
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Horizontal position `(r, y_l)` of the `l`-th ball. -/
def hpoint (r : ℝ) (y : ι → ℝ) (l : ι) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, y l]

/-- The unit normal `(1, 0)` of the section edge. -/
def nvec : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0]

/-- The section `D = {q | r < q₀}`. -/
def Dhalf (r : ℝ) : Set Plane := {q | r<q 0}

theorem hpoint_zero (r : ℝ) (y : ι → ℝ) (l : ι) : hpoint r y l 0=r := by simp [hpoint]

theorem hpoint_one (r : ℝ) (y : ι → ℝ) (l : ι) : hpoint r y l 1=y l := by simp [hpoint]

theorem nvec_zero : nvec 0=1 := by simp [nvec]

theorem nvec_one : nvec 1=0 := by simp [nvec]

theorem norm_nvec : ‖nvec‖=1 := by
  have h : ‖nvec‖^2=1 := by
    rw [norm_sq_plane, nvec_zero, nvec_one]
    norm_num
  nlinarith [norm_nonneg nvec]

theorem hD_half (r : ℝ) (y : ι → ℝ) (l : ι) (s : ℝ) :
    Dhalf r ∩ closedBall (hpoint r y l) s=(fun q => q-hpoint r y l) ⁻¹' (U nvec ∩ closedBall 0 s) := by
  ext q
  simp only [Dhalf, mem_inter_iff, mem_setOf_eq, mem_preimage, U, mem_closedBall, dist_zero_right,
    dist_eq_norm, sub_zero, ip_apply, nvec_zero, nvec_one, PiLp.sub_apply, hpoint_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩

theorem lam_pos (χ : ℝ) (hχ : 0<χ) : 0<(3*χ/(χ+3) : ℝ) := by positivity

theorem lam_ne (χ : ℝ) (hχ : 0<χ) : lam χ≠0 := by
  unfold lam
  exact Complex.ofReal_ne_zero.mpr (lam_pos χ hχ).ne'


/-- The unperturbed plane points `(r, y_l, 0)` of the interpolation theorem. -/
def pts (r : ℝ) (y : ι → ℝ) (l : ι) : Space := abovePoint (hpoint r y l) 0

/-- Prescribed jets `(E_z, H_x, H_y) = (-1/Λ, 0, 1)` at the own point of the `j`-th input. -/
def target (χ : ℝ) (e : ι ≃ Fin (Fintype.card ι)) (j : Fin (Fintype.card ι)) :
    RestrictedTEJetMap.Jet ι := fun q => if e q.1=j then ![-(lam χ)⁻¹, 0, 1] q.2 else 0

theorem sum_select {N : ℕ} (f : Fin N → ℂ) (i : Fin N) (v w : ℂ) :
    ∑ j, f j*(w*(if i=j then v else 0))=f i*(w*v) := by
  simp [mul_ite, Finset.sum_ite_eq]

theorem jets_of_interp (r : ℝ) (y : ι → ℝ) (scale : ℝ) (χ : ℝ) (e : ι ≃ Fin (Fintype.card ι))
    (A : Fin (Fintype.card ι) → Index →₀ ℂ)
    (hjet : ∀ j, RestrictedTEJetMap.fieldJet (pts r y) (A j)=(1/(Real.sqrt scale : ℂ)) • target χ e j)
    (cf : Fin (Fintype.card ι) → ℂ) (l : ι) :
    electric (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (hpoint r y l)) 2=
        cf (e l)*((1/(Real.sqrt scale : ℂ))*(-(lam χ)⁻¹)) ∧
      magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (hpoint r y l)) 0=0 ∧
      magnetic (∑ k, cf k • A k) (MaxwellPlaneTail.planePoint (hpoint r y l)) 1=
        cf (e l)*((1/(Real.sqrt scale : ℂ))*1) := by
  have hE (j : Fin (Fintype.card ι)) : electric (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 2=
      (1/(Real.sqrt scale : ℂ))*(if e l=j then -(lam χ)⁻¹ else 0) := by
    have h : electric (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 2=
        ((1/(Real.sqrt scale : ℂ)) • target χ e j) (l, 0) := congrFun (hjet j) (l, 0)
    rw [h]
    simp [target]
  have hH0 (j : Fin (Fintype.card ι)) : magnetic (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 0=
      (1/(Real.sqrt scale : ℂ))*(if e l=j then (0 : ℂ) else 0) := by
    have h : magnetic (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 0=
        ((1/(Real.sqrt scale : ℂ)) • target χ e j) (l, 1) := congrFun (hjet j) (l, 1)
    rw [h]
    simp [target]
  have hH1 (j : Fin (Fintype.card ι)) : magnetic (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 1=
      (1/(Real.sqrt scale : ℂ))*(if e l=j then (1 : ℂ) else 0) := by
    have h : magnetic (A j) (MaxwellPlaneTail.planePoint (hpoint r y l)) 1=
        ((1/(Real.sqrt scale : ℂ)) • target χ e j) (l, 2) := congrFun (hjet j) (l, 2)
    rw [h]
    simp [target]
  refine ⟨?_, ?_, ?_⟩
  · rw [electric_sum_apply]
    simp_rw [hE]
    exact sum_select cf (e l) _ _
  · rw [magnetic_sum_apply]
    simp_rw [hH0]
    simp
  · rw [magnetic_sum_apply]
    simp_rw [hH1]
    exact sum_select cf (e l) _ _


theorem kap_value (r : ℝ) (y : ι → ℝ) (ρ scale χ : ℝ) (hs : 0<scale) (hχ : 0<χ)
    (e : ι ≃ Fin (Fintype.card ι)) (A : Fin (Fintype.card ι) → Index →₀ ℂ)
    (hjet : ∀ j, RestrictedTEJetMap.fieldJet (pts r y) (A j)=(1/(Real.sqrt scale : ℂ)) • target χ e j)
    (cf : Fin (Fintype.card ι) → ℂ) (l : ι) :
    kap ρ χ (∑ k, cf k • A k) (hpoint r y) (fun _ => nvec) l=
      ((Vb ρ*‖cf (e l)‖^2/scale : ℝ) : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := jets_of_interp r y scale χ e A hjet cf l
  unfold kap mj
  rw [h1, h2, h3]
  simp only [nvec_zero, nvec_one, Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, sub_zero]
  have hΛ := lam_ne χ hχ
  have hsq : (Real.sqrt scale : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have hss : (Real.sqrt scale : ℂ)*(Real.sqrt scale : ℂ)=(scale : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
  have hcc : cf (e l)*conj (cf (e l))=((‖cf (e l)‖ : ℝ) : ℂ)^2 := Complex.mul_conj' _
  have hconj : conj (cf (e l)*(1/(Real.sqrt scale : ℂ)))=conj (cf (e l))*(1/(Real.sqrt scale : ℂ)) := by
    simp [map_mul, map_div₀, Complex.conj_ofReal]
  rw [hconj]
  push_cast
  have hscale : (scale : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [← hss] at hscale ⊢
  rw [← hcc]
  field_simp
  ring


theorem hpoint_inj (r : ℝ) (y : ι → ℝ) (hy : Function.Injective y) (l k : ι) (hlk : l≠k) :
    hpoint r y l≠hpoint r y k := by
  intro heq
  apply hlk
  apply hy
  have := congrArg (fun q : Plane => q 1) heq
  simpa [hpoint_one] using this

/-- The concrete explicit parity device: for `N` distinct points `(r, y_l, 0)` of one line there are `N`
orthonormal finite physical inputs (with their jets prescribed by the interpolation theorem) whose actual
complete flux through `D = {x > r}` has passage at least `ηt` and absolute bypass at most `δt` for every unit-power
vector of their span and all sufficiently small `a`, whenever `ηt < p0 < δt` for the explicit
`p0 = Vb ρ * halfPlane (1,0) h / scale`. The elementary geometric conditions (ball separation, containment, height)
are explicit hypotheses. -/
theorem concrete_counting (r : ℝ) (hr : r≠0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R b : ℝ) (hρ : 0<ρ) (hχ : 0<χ) (hh : ρ<h) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j →
      δ≤dist (abovePoint (hpoint r y i) (h*a)) (abovePoint (hpoint r y j) (h*a)))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖abovePoint (hpoint r y l) (h*a)‖+ρ≤R) :
    ∃ (scale : ℝ) (N : ℕ) (A : Fin N → Index →₀ ℂ), 0<scale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      ∀ ηt δt : ℝ, ηt<Vb ρ*halfPlane nvec h/scale → Vb ρ*halfPlane nvec h/scale<δt →
        ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A'∈Submodule.span ℂ (Set.range A),
          RestrictedTEIncoming.physicalPower A'=1 →
          ηt≤OQ14.RestrictedTEPassageTransfer.passage volume (Dhalf r)
              (Fflux (fun a l => abovePoint (hpoint r y l) (h*a)) ρ χ R b hρ hχ.le hi a A') ∧
          OQ14.RestrictedTEPassageTransfer.bypass volume (Dhalf r)
              (Fflux (fun a l => abovePoint (hpoint r y l) (h*a)) ρ χ R b hρ hχ.le hi a A')≤δt := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h0 : ∀ l, pts r y l 0=r := fun l => by simp [pts, abovePoint, hpoint]
  have h1 : ∀ l, pts r y l 1=y l := fun l => by simp [pts, abovePoint, hpoint]
  have h2 : ∀ l, pts r y l 2=0 := fun l => by simp [pts, abovePoint]
  obtain ⟨scale, hs, L, A, _, hjet, horth⟩ := PhysicalTEBandInterpolation.interpolate r hr y hy (pts r y)
    h0 h1 h2 (Fintype.card ι) (target χ e)
  refine ⟨scale, Fintype.card ι, A, hs, horth, ?_⟩
  intro ηt δt hlo hhi
  have hhpos : ∀ _ : ι, 0<h := fun _ => by linarith
  have hγ : 0<h-ρ := by linarith
  have hh' : ∀ a : ℝ, 0<a → a≤1 → ∀ l : ι, ((h-ρ)+ρ)*a≤
      |(abovePoint (hpoint r y l) (h*a)) 2| := by
    intro a ha _ l
    rw [above_normal, abs_of_pos (mul_pos (by linarith) ha)]
    linarith
  have hspan : ∀ A'∈Submodule.span ℂ (Set.range A), ∃ cf : Fin (Fintype.card ι) → ℂ, ∑ k, cf k • A k=A' :=
    fun A' hA' => (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA'
  have hT : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 0=
        -(mj A' (hpoint r y) (fun _ => nvec) l)*((nvec 1 : ℝ) : ℂ) ∧
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 1=
        mj A' (hpoint r y) (fun _ => nvec) l*((nvec 0 : ℝ) : ℂ) := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    obtain ⟨_, h2', h3'⟩ := jets_of_interp r y scale χ e A hjet cf l
    unfold mj
    rw [h2', h3']
    simp [nvec_zero, nvec_one]
  have hK : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      0≤(kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re ∧
        (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).im=0 := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    rw [kap_value r y ρ scale χ hs hχ e A hjet cf l, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have : 0≤Vb ρ := by unfold Vb; positivity
    positivity
  have hB : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ∑ l, (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re*halfPlane nvec h=
        Vb ρ*halfPlane nvec h/scale := by
    intro A' hA' hpow
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    have hsum : (∑ k, ‖cf k‖^2)=1 := by rw [← power_comb A horth cf]; exact hpow
    simp_rw [kap_value r y ρ scale χ hs hχ e A hjet cf, Complex.ofReal_re]
    have : (∑ l : ι, Vb ρ*‖cf (e l)‖^2/scale*halfPlane nvec h)=
        Vb ρ*halfPlane nvec h/scale*∑ l : ι, ‖cf (e l)‖^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [this, Equiv.sum_comp e (fun k => ‖cf k‖^2), hsum, mul_one]
  exact explicit_parity_device_counting (κ := Fin (Fintype.card ι))
    (fun a l => abovePoint (hpoint r y l) (h*a)) ρ χ δ R b (h-ρ) hρ hχ.le hδ hR hb hγ hsep hi hh'
    (hpoint r y) (fun _ => h) hhpos (fun a l => rfl) (hpoint_inj r y hy) (fun _ => nvec)
    (fun _ => norm_nvec) (Dhalf r) (fun l => ⟨1, one_pos, fun s _ _ => hD_half r y l s⟩) A horth hT hK
    (Vb ρ*halfPlane nvec h/scale) ηt δt hB hlo hhi

end OQ14.RestrictedTEConcreteDevice
#print axioms OQ14.RestrictedTEConcreteDevice.hpoint_zero
#print axioms OQ14.RestrictedTEConcreteDevice.hpoint_one
#print axioms OQ14.RestrictedTEConcreteDevice.nvec_zero
#print axioms OQ14.RestrictedTEConcreteDevice.nvec_one
#print axioms OQ14.RestrictedTEConcreteDevice.norm_nvec
#print axioms OQ14.RestrictedTEConcreteDevice.hD_half
#print axioms OQ14.RestrictedTEConcreteDevice.lam_pos
#print axioms OQ14.RestrictedTEConcreteDevice.lam_ne
#print axioms OQ14.RestrictedTEConcreteDevice.sum_select
#print axioms OQ14.RestrictedTEConcreteDevice.jets_of_interp
#print axioms OQ14.RestrictedTEConcreteDevice.kap_value
#print axioms OQ14.RestrictedTEConcreteDevice.hpoint_inj
#print axioms OQ14.RestrictedTEConcreteDevice.concrete_counting
