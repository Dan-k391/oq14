import RestrictedTEPlaneJets
import RestrictedTEPartnerBalls
import RestrictedTEEvenDatum

/-! Counted-channel inequalities for the doubled (partner-ball) explicit parity device.

The doubled family has index type `ι ⊕ ι`: the original balls at heights `h l a` above the plane positions `c l`
and their half-turn images above `-c l`.  By the half-turn covariance of the finite TE fields the jets of every
input at the partner points are determined by those at the original points, so the jet hypotheses of
`RestrictedTEPlaneJets.explicit_parity_device_counting` for the doubled family follow from those of the original
family, with passage constant `2 * p0`, provided the section `D` is symmetric under `q ↦ -q`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPartnerCount
open Complex MeasureTheory Metric Set Filter Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
open OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEPlaneJets
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane

theorem ip_neg_left (n ξ : Plane) : ip (-n) ξ=-ip n ξ := by
  unfold ip
  exact inner_neg_left n ξ

theorem psi_neg_left (n : Plane) (t : ℝ) (ξ : Plane) : psi (-n) t ξ=-psi n t ξ := by
  unfold psi
  rw [ip_neg_left]
  ring

/-- The half-plane profile integral is invariant under `n ↦ -n`. -/
theorem halfPlane_neg (n : Plane) (t : ℝ) : halfPlane (-n) t=halfPlane n t := by
  classical
  unfold halfPlane
  rw [← integral_neg_eq_self]
  congr 1
  funext ξ
  by_cases hξ : ξ∈U n
  · have h1 : -ξ∈U (-n) := by
      change 0 < ip (-n) (-ξ)
      rw [ip_neg_left, ip_neg]
      simpa using hξ
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem hξ, psi_neg_left, psi_neg]
    ring
  · have h1 : -ξ∉U (-n) := by
      intro h
      apply hξ
      change 0 < ip (-n) (-ξ) at h
      rw [ip_neg_left, ip_neg] at h
      change 0 < ip n ξ
      simpa using h
    rw [Set.indicator_of_not_mem h1, Set.indicator_of_not_mem hξ]

theorem rot_planePoint (q : Plane) :
    HalfTurnVectorAction.rot (MaxwellPlaneTail.planePoint q)=MaxwellPlaneTail.planePoint (-q) :=
  RestrictedTEPartnerBalls.rot_abovePoint q 0

/-- Jets of every input at a partner point are determined by those at the original point. -/
theorem partner_jets (A' : Index →₀ ℂ) (q : Plane) :
    electric A' (MaxwellPlaneTail.planePoint (-q)) 2=electric A' (MaxwellPlaneTail.planePoint q) 2 ∧
    magnetic A' (MaxwellPlaneTail.planePoint (-q)) 0=-magnetic A' (MaxwellPlaneTail.planePoint q) 0 ∧
    magnetic A' (MaxwellPlaneTail.planePoint (-q)) 1=-magnetic A' (MaxwellPlaneTail.planePoint q) 1 := by
  rw [← rot_planePoint]
  refine ⟨?_, ?_, ?_⟩
  · rw [RestrictedTEEvenDatum.electric_rot]
    simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]
  · rw [RestrictedTEEvenDatum.magnetic_rot]
    simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]
  · rw [RestrictedTEEvenDatum.magnetic_rot]
    simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The doubled plane positions, heights and normals. -/
def cD (c : ι → Plane) : ι ⊕ ι → Plane := Sum.elim c (fun l => -c l)

def hD' (h : ι → ℝ) : ι ⊕ ι → ℝ := Sum.elim h h

def nD (n : ι → Plane) : ι ⊕ ι → Plane := Sum.elim n (fun l => -n l)

theorem mj_partner (A' : Index →₀ ℂ) (c n : ι → Plane) (l : ι) :
    mj A' (cD c) (nD n) (Sum.inr l)=mj A' c n l := by
  obtain ⟨_, h0, h1⟩ := partner_jets A' (c l)
  unfold mj cD nD
  simp only [Sum.elim_inr, Sum.elim_inl, PiLp.neg_apply, h0, h1]
  push_cast
  ring

theorem kap_partner (ρ χ : ℝ) (A' : Index →₀ ℂ) (c n : ι → Plane) (l : ι) :
    kap ρ χ A' (cD c) (nD n) (Sum.inr l)=kap ρ χ A' c n l := by
  obtain ⟨he, _, _⟩ := partner_jets A' (c l)
  unfold kap
  rw [mj_partner]
  simp only [cD, Sum.elim_inr, Sum.elim_inl, he]

theorem kap_orig (ρ χ : ℝ) (A' : Index →₀ ℂ) (c n : ι → Plane) (l : ι) :
    kap ρ χ A' (cD c) (nD n) (Sum.inl l)=kap ρ χ A' c n l := rfl

/-- Counted-channel inequalities for the doubled (partner-ball) parity device. -/
theorem doubled_device_counting (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j : ι ⊕ ι, i≠j →
      δ≤dist (RestrictedTEPartnerBalls.partnerCentre (p a) i) (RestrictedTEPartnerBalls.partnerCentre (p a) j))
    (hi : ∀ a, 0<a → a≤1 → ∀ j : ι ⊕ ι, ‖RestrictedTEPartnerBalls.partnerCentre (p a) j‖+ρ≤R)
    (hh' : ∀ a, 0<a → a≤1 → ∀ j : ι ⊕ ι,
      (γ+ρ)*a≤|RestrictedTEPartnerBalls.partnerCentre (p a) j 2|)
    (c : ι → Plane) (h : ι → ℝ) (hhpos : ∀ l, 0<h l) (hp : ∀ a l, p a l=abovePoint (c l) (h l*a))
    (hcd : ∀ i j : ι ⊕ ι, i≠j → cD c i≠cD c j) (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (D : Set Plane)
    (hDsym : ∀ q : Plane, -q∈D ↔ q∈D)
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
    (hη : ηt<2*p0) (hδt : 2*p0<δt) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ηt≤OQ14.RestrictedTEPassageTransfer.passage volume D
        (Fflux (fun a => RestrictedTEPartnerBalls.partnerCentre (p a)) ρ χ R b hρ hχ hi a A') ∧
      OQ14.RestrictedTEPassageTransfer.bypass volume D
        (Fflux (fun a => RestrictedTEPartnerBalls.partnerCentre (p a)) ρ χ R b hρ hχ hi a A')≤δt := by
  have hp' : ∀ a (j : ι ⊕ ι), RestrictedTEPartnerBalls.partnerCentre (p a) j=
      abovePoint (cD c j) (hD' h j*a) := by
    intro a j
    rcases j with l | l
    · exact hp a l
    · simp only [RestrictedTEPartnerBalls.partnerCentre, cD, hD', Sum.elim_inr, hp a l]
      exact RestrictedTEPartnerBalls.rot_abovePoint (c l) (h l*a)
  have hhpos' : ∀ j : ι ⊕ ι, 0<hD' h j := by
    intro j
    rcases j with l | l <;> simpa [hD'] using hhpos l
  have hn' : ∀ j : ι ⊕ ι, ‖nD n j‖=1 := by
    intro j
    rcases j with l | l
    · simpa [nD] using hn l
    · simpa [nD, norm_neg] using hn l
  have hD'' : ∀ j : ι ⊕ ι, ∃ s0 : ℝ, 0<s0 ∧ ∀ s : ℝ, 0<s → s≤s0 →
      D ∩ closedBall (cD c j) s=(fun q => q-cD c j) ⁻¹' (U (nD n j) ∩ closedBall 0 s) := by
    intro j
    rcases j with l | l
    · simpa [cD, nD] using hD l
    · obtain ⟨s0, hs0, hs⟩ := hD l
      refine ⟨s0, hs0, fun s hs1 hs2 => ?_⟩
      have hset := hs s hs1 hs2
      ext q
      have hq := Set.ext_iff.mp hset (-q)
      simp only [mem_inter_iff, mem_preimage, mem_closedBall, dist_zero_right, sub_zero, dist_eq_norm, U,
        mem_setOf_eq] at hq
      have e1 : -q-c l=-(q-(-c l)) := by abel
      rw [e1, norm_neg, ip_neg, hDsym] at hq
      simp only [cD, nD, Sum.elim_inr, mem_inter_iff, mem_preimage, mem_closedBall, dist_zero_right, sub_zero,
        dist_eq_norm, U, mem_setOf_eq, ip_neg_left]
      exact hq
  have hT' : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ j : ι ⊕ ι,
      magnetic A' (MaxwellPlaneTail.planePoint (cD c j)) 0=
        -(mj A' (cD c) (nD n) j)*((nD n j 1 : ℝ) : ℂ) ∧
      magnetic A' (MaxwellPlaneTail.planePoint (cD c j)) 1=
        mj A' (cD c) (nD n) j*((nD n j 0 : ℝ) : ℂ) := by
    intro A' hA' hpw j
    rcases j with l | l
    · exact HT A' hA' hpw l
    · obtain ⟨_, h0, h1⟩ := partner_jets A' (c l)
      obtain ⟨T0, T1⟩ := HT A' hA' hpw l
      refine ⟨?_, ?_⟩
      · show magnetic A' (MaxwellPlaneTail.planePoint (-c l)) 0=
          -(mj A' (cD c) (nD n) (Sum.inr l))*(((-n l) 1 : ℝ) : ℂ)
        rw [h0, mj_partner, T0]
        simp
      · show magnetic A' (MaxwellPlaneTail.planePoint (-c l)) 1=
          mj A' (cD c) (nD n) (Sum.inr l)*(((-n l) 0 : ℝ) : ℂ)
        rw [h1, mj_partner, T1]
        simp
  have hK' : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ j : ι ⊕ ι,
      0≤(kap ρ χ A' (cD c) (nD n) j).re ∧ (kap ρ χ A' (cD c) (nD n) j).im=0 := by
    intro A' hA' hpw j
    rcases j with l | l
    · exact HK A' hA' hpw l
    · rw [kap_partner]
      exact HK A' hA' hpw l
  have hB' : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ∑ j : ι ⊕ ι, (kap ρ χ A' (cD c) (nD n) j).re*halfPlane (nD n j) (hD' h j)=2*p0 := by
    intro A' hA' hpw
    rw [Fintype.sum_sum_type]
    have h1 : ∑ l : ι, (kap ρ χ A' (cD c) (nD n) (Sum.inl l)).re*halfPlane (nD n (Sum.inl l)) (hD' h (Sum.inl l))=p0 :=
      HB A' hA' hpw
    have h2 : ∑ l : ι, (kap ρ χ A' (cD c) (nD n) (Sum.inr l)).re*halfPlane (nD n (Sum.inr l)) (hD' h (Sum.inr l))=p0 := by
      rw [← HB A' hA' hpw]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [kap_partner]
      simp only [nD, hD', Sum.elim_inr]
      rw [halfPlane_neg]
    rw [h1, h2]
    ring
  exact explicit_parity_device_counting (κ := κ) (fun a => RestrictedTEPartnerBalls.partnerCentre (p a)) ρ χ δ R b γ
    hρ hχ hδ hR hb hγ hsep hi hh' (cD c) (hD' h) hhpos' hp' hcd (nD n) hn' D hD'' A horth hT' hK'
    (2*p0) ηt δt hB' hη hδt

end OQ14.RestrictedTEPartnerCount
#print axioms OQ14.RestrictedTEPartnerCount.ip_neg_left
#print axioms OQ14.RestrictedTEPartnerCount.psi_neg_left
#print axioms OQ14.RestrictedTEPartnerCount.halfPlane_neg
#print axioms OQ14.RestrictedTEPartnerCount.rot_planePoint
#print axioms OQ14.RestrictedTEPartnerCount.partner_jets
#print axioms OQ14.RestrictedTEPartnerCount.mj_partner
#print axioms OQ14.RestrictedTEPartnerCount.kap_partner
#print axioms OQ14.RestrictedTEPartnerCount.kap_orig
#print axioms OQ14.RestrictedTEPartnerCount.doubled_device_counting
