import RestrictedTEConcreteDevice
import RestrictedTEPartnerCount

/-! The concrete doubled (partner-ball) parity device: the balls of `RestrictedTEConcreteDevice` on the line
`x = r` together with their half-turn images on the line `x = -r`, and the half-turn symmetric section
`D = {|x| > r}` whose edges pass through all the dipole positions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEConcreteDoubled
open Complex MeasureTheory Metric Set Filter Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
open OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEPlaneJets
open OQ14.RestrictedTEConcreteDevice OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerBalls
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The half-turn symmetric section `{|x| > r}`. -/
def Dsym (r : ℝ) : Set Plane := {q | r < |q 0|}

theorem Dsym_neg (r : ℝ) (q : Plane) : -q∈Dsym r ↔ q∈Dsym r := by
  simp [Dsym, abs_neg]

theorem hD_sym (r : ℝ) (y : ι → ℝ) (l : ι) (s : ℝ) (hsr : s≤r) :
    Dsym r ∩ closedBall (hpoint r y l) s=(fun q => q-hpoint r y l) ⁻¹' (U nvec ∩ closedBall 0 s) := by
  ext q
  have hn := PiLp.norm_apply_le (q-hpoint r y l) 0
  rw [Real.norm_eq_abs] at hn
  simp only [Dsym, mem_inter_iff, mem_setOf_eq, mem_preimage, U, mem_closedBall, dist_zero_right, sub_zero,
    dist_eq_norm, ip_apply, nvec_zero, nvec_one, PiLp.sub_apply, hpoint_zero] at hn ⊢
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : |q 0-r|≤s := hn.trans h2
    have h4 : 0≤q 0 := by
      have := (abs_le.mp h3).1
      linarith
    rw [abs_of_nonneg h4] at h1
    exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    have h4 : r<q 0 := by linarith
    exact ⟨lt_of_lt_of_le h4 (le_abs_self _), h2⟩

theorem partner_hi_aux (p : ℝ → ι → Space) (ρ R : ℝ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) :
    ∀ a, 0<a → a≤1 → ∀ j : ι ⊕ ι, ‖partnerCentre (p a) j‖+ρ≤R := by
  intro a ha ha1 j
  rcases j with l | l
  · simpa [partnerCentre] using hi a ha ha1 l
  · simpa [partnerCentre, HalfTurnVectorAction.rot.norm_map] using hi a ha ha1 l

theorem partner_hh_aux (p : ℝ → ι → Space) (γ ρ : ℝ)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) :
    ∀ a, 0<a → a≤1 → ∀ j : ι ⊕ ι, (γ+ρ)*a≤|partnerCentre (p a) j 2| := by
  intro a ha ha1 j
  obtain ⟨l, hl⟩ := partner_height (p a) j
  rw [hl]
  exact hh a ha ha1 l

/-- The concrete doubled parity device: `2N` balls (the original ones above `(r, y_l, 0)` and their half-turn
images above `(-r, -y_l, 0)`), orthonormal inputs from the interpolation theorem, and the symmetric section
`D = {|x| > r}`.  The doubled passage constant is `2 * p0`. -/
theorem concrete_doubled_counting (r : ℝ) (hr : 0<r) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R b : ℝ) (hρ : 0<ρ) (hχ : 0<χ) (hh : ρ<h) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j →
      δ≤dist (abovePoint (hpoint r y i) (h*a)) (abovePoint (hpoint r y j) (h*a)))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖abovePoint (hpoint r y l) (h*a)‖+ρ≤R) :
    ∃ (scale : ℝ) (N : ℕ) (A : Fin N → Index →₀ ℂ), 0<scale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      ∀ ηt δt : ℝ, ηt<2*(Vb ρ*halfPlane nvec h/scale) → 2*(Vb ρ*halfPlane nvec h/scale)<δt →
        ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A'∈Submodule.span ℂ (Set.range A),
          RestrictedTEIncoming.physicalPower A'=1 →
          ηt≤OQ14.RestrictedTEPassageTransfer.passage volume (Dsym r)
              (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h*a))) ρ χ R b hρ hχ.le
                (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h*a)) ρ R hi) a A') ∧
          OQ14.RestrictedTEPassageTransfer.bypass volume (Dsym r)
              (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h*a))) ρ χ R b hρ hχ.le
                (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h*a)) ρ R hi) a A')≤δt := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hr0 : r≠0 := hr.ne'
  have h0 : ∀ l, pts r y l 0=r := fun l => by simp [pts, abovePoint, hpoint]
  have h1 : ∀ l, pts r y l 1=y l := fun l => by simp [pts, abovePoint, hpoint]
  have h2 : ∀ l, pts r y l 2=0 := fun l => by simp [pts, abovePoint]
  obtain ⟨scale, hs, L, A, _, hjet, horth⟩ := PhysicalTEBandInterpolation.interpolate r hr0 y hy (pts r y)
    h0 h1 h2 (Fintype.card ι) (target χ e)
  refine ⟨scale, Fintype.card ι, A, hs, horth, ?_⟩
  intro ηt δt hlo hhi
  have hhpos : ∀ _ : ι, 0<h := fun _ => by linarith
  have hγ : 0<h-ρ := by linarith
  have hh1 : ∀ a : ℝ, 0<a → a≤1 → ∀ l : ι, ((h-ρ)+ρ)*a≤
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
  have hsepD : ∀ a : ℝ, 0<a → a≤1 → ∀ i j : ι ⊕ ι, i≠j → min δ (2*|r|)≤
      dist (partnerCentre (fun l => abovePoint (hpoint r y l) (h*a)) i)
        (partnerCentre (fun l => abovePoint (hpoint r y l) (h*a)) j) :=
    fun a _ _ => partner_separation r δ (h*a) (hpoint r y) (fun l => hpoint_zero r y l) (hsep a ‹_› ‹_›)
  have hδ' : 0<min δ (2*|r|) := lt_min hδ (by positivity)
  have hcdD : ∀ i j : ι ⊕ ι, i≠j → cD (hpoint r y) i≠cD (hpoint r y) j := by
    intro i j hij heq
    simp only [cD] at heq
    rcases i with l | l <;> rcases j with k | k
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) heq
    · have := congrArg (fun q : Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · have := congrArg (fun q : Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) (neg_inj.mp heq)
  exact doubled_device_counting (fun a l => abovePoint (hpoint r y l) (h*a)) ρ χ (min δ (2*|r|)) R b (h-ρ)
    hρ hχ.le hδ' hR hb hγ hsepD (partner_hi_aux _ ρ R hi) (partner_hh_aux _ (h-ρ) ρ hh1)
    (hpoint r y) (fun _ => h) hhpos (fun a l => rfl) hcdD (fun _ => nvec) (fun _ => norm_nvec) (Dsym r)
    (Dsym_neg r) (fun l => ⟨r, hr, fun s _ hs => hD_sym r y l s hs⟩) A horth hT hK
    (Vb ρ*halfPlane nvec h/scale) ηt δt hB hlo hhi

end OQ14.RestrictedTEConcreteDoubled
#print axioms OQ14.RestrictedTEConcreteDoubled.Dsym_neg
#print axioms OQ14.RestrictedTEConcreteDoubled.hD_sym
#print axioms OQ14.RestrictedTEConcreteDoubled.partner_hi_aux
#print axioms OQ14.RestrictedTEConcreteDoubled.partner_hh_aux
#print axioms OQ14.RestrictedTEConcreteDoubled.concrete_doubled_counting
