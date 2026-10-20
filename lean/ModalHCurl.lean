import ModalLocal
import WeakPoynting.RegionalCurlUpgrade

/-! # Actual regional H(curl) spherical modes at complex frequency

The graph elements contain the actual assembled fields and their actual
Maxwell curls. Smooth compact test identities are upgraded by the proved
support-controlled density theorem. No global L2 condition is imposed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ModalHCurl

open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ModalWeak OQ14.ModalLocal
  OQ14.ModalProfiles OQ14.ModalMatching OQ14.ModalInterface
open scoped Topology

def electricCurl (n k a b : ℂ) : Field := fun x j => I*k*magnetic n k a b x j

def magneticCurl (n k a b : ℂ) : Field :=
  fun x j => -I*k*coefficient n x*electric n k a b x j

theorem electricCurl_memLp (n k a b : ℂ) (hk : k ≠ 0)
    (Ω : Set Space) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    MemLp (fun x => electricCurl n k a b x j) 2 (DomainCurl.regionMeasure Ω) :=
  (magnetic_memLp_bounded n k a b hk Ω hbΩ 2 j).const_mul (I*k)

theorem magneticCurl_memLp (n k a b : ℂ) (hk : k ≠ 0)
    (Ω : Set Space) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    MemLp (fun x => magneticCurl n k a b x j) 2 (DomainCurl.regionMeasure Ω) := by
  simpa only [magneticCurl, mul_assoc] using
    (displacement_memLp_bounded n k a b hk Ω hbΩ 2 j).const_mul (-I*k)

theorem electric_hasWeakCurl (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) :
    DomainCurl.HasWeakCurl Ω
      (DomainCurl.fieldToL2 Ω (electric n k a b)
        (electric_memLp_bounded n k a b hk Ω hbΩ 2))
      (DomainCurl.fieldToL2 Ω (electricCurl n k a b)
        (electricCurl_memLp n k a b hk Ω hbΩ)) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ
  intro f hf hc _ j
  have hf2 : ContDiff ℝ 2 f :=
    hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := congrFun (assembled_weak_maxwell n k a b hn hk hm f hf2 hc).1 j
  fin_cases j <;>
    simpa [electricCurl, WeakCurl.next, WeakCurl.previous, weakCurlPairing] using he.symm

theorem magnetic_hasWeakCurl (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) :
    DomainCurl.HasWeakCurl Ω
      (DomainCurl.fieldToL2 Ω (magnetic n k a b)
        (magnetic_memLp_bounded n k a b hk Ω hbΩ 2))
      (DomainCurl.fieldToL2 Ω (magneticCurl n k a b)
        (magneticCurl_memLp n k a b hk Ω hbΩ)) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ
  intro f hf hc _ j
  have hf2 : ContDiff ℝ 2 f :=
    hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := congrFun (assembled_weak_maxwell n k a b hn hk hm f hf2 hc).2 j
  fin_cases j <;>
    simpa [magneticCurl, WeakCurl.next, WeakCurl.previous, weakCurlPairing] using he.symm

def electricGraph (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) : DomainCurl.HCurl Ω :=
  ⟨(DomainCurl.fieldToL2 Ω (electric n k a b) (electric_memLp_bounded n k a b hk Ω hbΩ 2),
    DomainCurl.fieldToL2 Ω (electricCurl n k a b) (electricCurl_memLp n k a b hk Ω hbΩ)),
    electric_hasWeakCurl n k a b hn hk hm Ω hΩ hbΩ⟩

def magneticGraph (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) : DomainCurl.HCurl Ω :=
  ⟨(DomainCurl.fieldToL2 Ω (magnetic n k a b) (magnetic_memLp_bounded n k a b hk Ω hbΩ 2),
    DomainCurl.fieldToL2 Ω (magneticCurl n k a b) (magneticCurl_memLp n k a b hk Ω hbΩ)),
    magnetic_hasWeakCurl n k a b hn hk hm Ω hΩ hbΩ⟩

theorem electricGraph_field_ae (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    ((electricGraph n k a b hn hk hm Ω hΩ hbΩ).val.1 j : Space → ℂ)
      =ᵐ[DomainCurl.regionMeasure Ω] fun x => electric n k a b x j :=
  (electric_memLp_bounded n k a b hk Ω hbΩ 2 j).coeFn_toLp

theorem magneticGraph_field_ae (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    ((magneticGraph n k a b hn hk hm Ω hΩ hbΩ).val.1 j : Space → ℂ)
      =ᵐ[DomainCurl.regionMeasure Ω] fun x => magnetic n k a b x j :=
  (magnetic_memLp_bounded n k a b hk Ω hbΩ 2 j).coeFn_toLp

theorem electricGraph_curl_ae (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    ((electricGraph n k a b hn hk hm Ω hΩ hbΩ).val.2 j : Space → ℂ)
      =ᵐ[DomainCurl.regionMeasure Ω] fun x => I*k*magnetic n k a b x j :=
  (electricCurl_memLp n k a b hk Ω hbΩ j).coeFn_toLp

theorem magneticGraph_curl_ae (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    ((magneticGraph n k a b hn hk hm Ω hΩ hbΩ).val.2 j : Space → ℂ)
      =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => -I*k*coefficient n x*electric n k a b x j :=
  (magneticCurl_memLp n k a b hk Ω hbΩ j).coeFn_toLp

/-- The actual graph representatives obey the coupled Maxwell equations at
complex frequency almost everywhere on the bounded open region. -/
theorem graph_maxwell_ae (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hm : matching 1 n k (a,b) = 0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (hbΩ : Bornology.IsBounded Ω) :
    ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      (electricGraph n k a b hn hk hm Ω hΩ hbΩ).val.2 j x =
        I*k*(magneticGraph n k a b hn hk hm Ω hΩ hbΩ).val.1 j x ∧
      (magneticGraph n k a b hn hk hm Ω hΩ hbΩ).val.2 j x =
        -I*k*coefficient n x*(electricGraph n k a b hn hk hm Ω hΩ hbΩ).val.1 j x := by
  apply ae_all_iff.mpr
  intro j
  filter_upwards [electricGraph_field_ae n k a b hn hk hm Ω hΩ hbΩ j,
    magneticGraph_field_ae n k a b hn hk hm Ω hΩ hbΩ j,
    electricGraph_curl_ae n k a b hn hk hm Ω hΩ hbΩ j,
    magneticGraph_curl_ae n k a b hn hk hm Ω hΩ hbΩ j] with x he hh hc hd
  simp only [he, hh, hc, hd, and_self]

theorem electric_continuousAt_exterior (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : 1 < ‖x‖) (j : Fin 3) :
    ContinuousAt (fun y => electric n k a b y j) x := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  have hx1 : ‖x‖ ≠ 1 := ne_of_gt hx
  have he : electric n k a b =ᶠ[𝓝 x]
      (fun y i => potentialGradient n k a b y i + axial n k a b y i) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    exact electric_decomposition n k a b hk y hy
  exact (((potentialGradient_differentiableAt n k a b hk x hx0 hx1 j).add
    (axial_differentiableAt n k a b hk x hx0 hx1 j)).congr_of_eventuallyEq
      (he.fun_comp (fun v => v j))).continuousAt

theorem magnetic_continuousAt_exterior (n k a b : ℂ) (hk : k ≠ 0)
    (x : Space) (hx : 1 < ‖x‖) (j : Fin 3) :
    ContinuousAt (fun y => magnetic n k a b y j) x := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  exact (magnetic_differentiableAt n k a b hk x hx0 (ne_of_gt hx) j).continuousAt

theorem fieldToL2_zero_on_open (Ω : Set Space) (F : Field)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (DomainCurl.regionMeasure Ω))
    (hz : DomainCurl.fieldToL2 Ω F hF = 0)
    (V : Set Space) (hV : IsOpen V) (hsub : V ⊆ Ω)
    (hc : ∀ j, ContinuousOn (fun x => F x j) V) :
    ∀ x ∈ V, F x = 0 := by
  have he (j : Fin 3) : (fun x => F x j) =ᵐ[DomainCurl.regionMeasure Ω] 0 := by
    apply (hF j).coeFn_toLp.symm.trans
    change ((DomainCurl.fieldToL2 Ω F hF j) : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω] 0
    rw [congrFun hz j]
    exact Lp.coeFn_zero ℂ 2 (DomainCurl.regionMeasure Ω)
  intro x hx
  ext j
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub (he j))
    hV (hc j) continuousOn_const hx

/-- Nonzero outgoing amplitude gives a genuinely nonzero regional graph
element, not merely a nonzero value on a null set. -/
theorem graphs_not_both_zero (n k a b : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (hb : b ≠ 0)
    (hm : matching 1 n k (a,b) = 0) :
    electricGraph n k a b hn hk hm (ball 0 2) isOpen_ball isBounded_ball ≠ 0 ∨
      magneticGraph n k a b hn hk hm (ball 0 2) isOpen_ball isBounded_ball ≠ 0 := by
  by_contra hz
  push_neg at hz
  let V : Set Space := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hs : V ⊆ ball (0 : Space) 2 := by intro x hx; exact mem_ball_zero_iff.mpr hx.2
  have he := fieldToL2_zero_on_open (ball 0 2) (electric n k a b)
    (electric_memLp_bounded n k a b hk _ isBounded_ball 2)
    (congrArg (fun u : DomainCurl.HCurl (ball 0 2) => u.val.1) hz.1) V hV hs
    (fun j x hx => (electric_continuousAt_exterior n k a b hk x hx.1 j).continuousWithinAt)
  have hh := fieldToL2_zero_on_open (ball 0 2) (magnetic n k a b)
    (magnetic_memLp_bounded n k a b hk _ isBounded_ball 2)
    (congrArg (fun u : DomainCurl.HCurl (ball 0 2) => u.val.1) hz.2) V hV hs
    (fun j x hx => (magnetic_continuousAt_exterior n k a b hk x hx.1 j).continuousWithinAt)
  obtain ⟨x, hx, ht⟩ := outer_traces_not_both_zero k b hk hb (3/2) (by norm_num)
  have hxV : x ∈ V := by dsimp [V]; rw [hx]; constructor <;> norm_num
  have hxt := assembled_exterior n k a b x hxV.1
  have he0 : outerE k b x = 0 := hxt.1.symm.trans (he x hxV)
  have hh0 : outerH k b x = 0 := hxt.2.symm.trans (hh x hxV)
  rcases ht with ht | ht
  · exact ht (by simp [he0, tangent])
  · exact ht (by simp [hh0, tangent])

/-- Actual nonzero regional H(curl) Maxwell fields of arbitrarily high
quality ratio. Their representatives are the explicit regular-interior and
outgoing-exterior fields. This is not a claim of full resolvent-pole isolation. -/
theorem exists_high_quality_hcurl_fields (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k a b : ℂ, ∃ E H : DomainCurl.HCurl (ball 0 2),
      k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ L < k.re ∧ k.im < 0 ∧
      Q < k.re / (-2 * k.im) ∧ (E ≠ 0 ∨ H ≠ 0) ∧
      (∀ᵐ x ∂DomainCurl.regionMeasure (ball 0 2), ∀ j : Fin 3,
        E.val.1 j x = electric (n : ℂ) k a b x j ∧
        H.val.1 j x = magnetic (n : ℂ) k a b x j) ∧
      (∀ᵐ x ∂DomainCurl.regionMeasure (ball 0 2), ∀ j : Fin 3,
        E.val.2 j x = I*k*H.val.1 j x ∧
        H.val.2 j x = -I*k*coefficient (n : ℂ) x*E.val.1 j x) := by
  obtain ⟨k, a, b, hk, ha, hb, hL, hi, hratio, hmatch, -, -, -⟩ :=
    exists_high_quality_transmission_fields n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hm : matching 1 (n : ℂ) k (a,b) = 0 := by
    simpa using sphere_matches_implies_matching (n : ℂ) k hn0 hk 1 (by norm_num) (a,b) hmatch
  refine ⟨k, a, b,
    electricGraph (n : ℂ) k a b hn0 hk hm (ball 0 2) isOpen_ball isBounded_ball,
    magneticGraph (n : ℂ) k a b hn0 hk hm (ball 0 2) isOpen_ball isBounded_ball,
    hk, ha, hb, hL, hi, hratio,
    graphs_not_both_zero (n : ℂ) k a b hn0 hk hb hm, ?_,
    graph_maxwell_ae (n : ℂ) k a b hn0 hk hm (ball 0 2) isOpen_ball isBounded_ball⟩
  apply ae_all_iff.mpr
  intro j
  filter_upwards [electricGraph_field_ae (n : ℂ) k a b hn0 hk hm _ isOpen_ball isBounded_ball j,
    magneticGraph_field_ae (n : ℂ) k a b hn0 hk hm _ isOpen_ball isBounded_ball j] with x he hh
  exact ⟨he, hh⟩

end OQ14.ModalHCurl

#print axioms OQ14.ModalHCurl.electricCurl_memLp
#print axioms OQ14.ModalHCurl.magneticCurl_memLp
#print axioms OQ14.ModalHCurl.electric_hasWeakCurl
#print axioms OQ14.ModalHCurl.magnetic_hasWeakCurl
#print axioms OQ14.ModalHCurl.electricGraph_field_ae
#print axioms OQ14.ModalHCurl.magneticGraph_field_ae
#print axioms OQ14.ModalHCurl.electricGraph_curl_ae
#print axioms OQ14.ModalHCurl.magneticGraph_curl_ae
#print axioms OQ14.ModalHCurl.graph_maxwell_ae
#print axioms OQ14.ModalHCurl.electric_continuousAt_exterior
#print axioms OQ14.ModalHCurl.magnetic_continuousAt_exterior
#print axioms OQ14.ModalHCurl.fieldToL2_zero_on_open
#print axioms OQ14.ModalHCurl.graphs_not_both_zero
#print axioms OQ14.ModalHCurl.exists_high_quality_hcurl_fields
