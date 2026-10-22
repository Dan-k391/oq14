import RadialParityLimit

/-! Common bounded radial families, equal to the literal finite stacks at large radius.
The small-radius empty definition only supplies a globally valid family for the
uniform scalar tail bounds. Spatial Maxwell reconstruction remains separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialPairedFamily
open Set Filter Complex OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
open scoped Topology

def ready (gs : List Segment) (R : ℝ) : Prop := 0 < R ∧ width gs ≤ R
instance (gs : List Segment) (R : ℝ) : Decidable (ready gs R) := Classical.propDecidable _

def family (gs : List Segment) (R : ℝ) : List Layer :=
  if h : ready gs R then layers gs R h.1 else []
def outer (gs : List Segment) (R : ℝ) : ℝ := if ready gs R then R+width gs else R

theorem family_chain (gs : List Segment) (R : ℝ) : Chain (family gs R) (outer gs R) R := by
  unfold family outer
  split_ifs with h
  · exact layers_chain gs R h.1
  · exact Chain.nil R

theorem outer_le_double (gs : List Segment) (R : ℝ) (hR : 0 ≤ R) : outer gs R ≤ 2*R := by
  unfold outer
  split_ifs with h
  · have hw := h.2
    linarith
  · linarith

theorem width_bound (gs : List Segment) (R : ℝ) : outer gs R-R ≤ width gs := by
  unfold outer
  split_ifs
  · simp
  · simpa only [sub_self] using width_nonnegative gs

theorem eventually_literal (gs : List Segment) :
    ∀ᶠ R : ℝ in atTop, ∃ hR : 0 < R, family gs R = layers gs R hR ∧ outer gs R = R+width gs := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),eventually_ge_atTop (width gs)] with R hR hw
  exact ⟨hR,by simp [family,outer,ready,hR,hw],by simp [outer,ready,hR,hw]⟩

theorem layers_parameters (gs : List Segment) (R : ℝ) (hR : 0 < R) (P : ℝ → ℝ → Prop)
    (hp : ∀ g ∈ gs, P g.q g.σ) : ∀ g ∈ layers gs R hR, P g.q g.σ := by
  induction gs generalizing R with
  | nil => simp [layers]
  | cons g gs ih =>
    intro v hv
    simp only [layers,List.mem_append,List.mem_singleton] at hv
    rcases hv with hv|rfl
    · exact ih (R+g.width) (add_pos_of_pos_of_nonneg hR g.width_nonneg)
        (fun w hw => hp w (List.mem_cons_of_mem _ hw)) v hv
    · exact hp g List.mem_cons_self

theorem family_parameters (gs : List Segment) (P : ℝ → ℝ → Prop)
    (hp : ∀ g ∈ gs, P g.q g.σ) (R : ℝ) : ∀ g ∈ family gs R, P g.q g.σ := by
  unfold family
  split_ifs with h
  · exact layers_parameters gs R h.1 P hp
  · simp

theorem pair_width (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (n : ℕ) :
    width (pairs q σ hq hσ n) = (n : ℝ)*(Real.pi/(2*q)+Real.pi/2) := by
  induction n with
  | zero => simp [pairs,width]
  | succ n ih => simp only [pairs,width,high,low,ih,Nat.cast_add,Nat.cast_one]; ring

theorem pairs_parameters (q σ : ℝ) (hq : 1 ≤ q) (hσ : 1 ≤ σ) (hσq : σ ≤ q^2) (n : ℕ) :
    ∀ g ∈ pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) n,
      1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2 ∧ g.q ≤ q := by
  have hq2 : 1 ≤ q^2 := by nlinarith
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    intro g hg
    simp only [pairs,List.mem_cons] at hg
    rcases hg with rfl|rfl|hg
    · exact ⟨hσ,hσq,le_rfl,le_rfl⟩
    · exact ⟨le_rfl,hq2,by simpa [low] using hq2,hq⟩
    · exact ih g hg

theorem paired_family_parameters (q σ : ℝ) (hq : 1 ≤ q) (hσ : 1 ≤ σ)
    (hσq : σ ≤ q^2) (n : ℕ) (R : ℝ) :
    ∀ g ∈ family (pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) n) R,
      1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2 ∧ g.q ≤ q :=
  family_parameters _ (fun qg σg => 1 ≤ σg ∧ σg ≤ q^2 ∧ qg^2 ≤ q^2 ∧ qg ≤ q)
    (pairs_parameters q σ hq hσ hσq n) R

def gamma (l : ℕ) (gs : List Segment) (R : ℝ) : ℂ :=
  if hR : 0 < R then RadialSource.gamma l (family gs R) R (outer gs R) hR else 0

theorem family_gamma_limit (l : ℕ) (gs : List Segment) :
    Tendsto (fun n : ℕ => gamma l gs (radius n)) atTop
      (𝓝 ((limitingCoefficients l gs).1/(limitingCoefficients l gs).2)) := by
  apply (actual_gamma_limit l gs).congr'
  filter_upwards [radius_tendsto.eventually (eventually_literal gs)] with n hn
  obtain ⟨hr,hg,hx⟩ := hn
  simp only [gamma,dif_pos (radius_pos n),hg,hx]

theorem family_even_limit (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    Tendsto (fun k : ℕ => gamma (2*j) (pairs q σ hq hσ n) (radius k)) atTop
      (𝓝 (-I*(((q/σ)^(2*n) : ℝ) : ℂ))) := by
  simpa only [RadialParityLimit.even_ratio j n q σ hq hσ] using
    family_gamma_limit (2*j) (pairs q σ hq hσ n)

theorem family_odd_limit (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    Tendsto (fun k : ℕ => gamma (2*j+1) (pairs q σ hq hσ n) (radius k)) atTop
      (𝓝 (-I*(((σ/q)^(2*n) : ℝ) : ℂ))) := by
  simpa only [RadialParityLimit.odd_ratio j n q σ hq hσ] using
    family_gamma_limit (2*j+1) (pairs q σ hq hσ n)

def te (q : ℝ) (hq : 0 < q) (n : ℕ) : List Segment := pairs q 1 hq zero_lt_one n
def tm (q : ℝ) (hq : 0 < q) (n : ℕ) : List Segment := pairs q (q^2) hq (sq_pos_of_pos hq) n

theorem te_even_limit (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun k : ℕ => gamma (2*j) (te q hq n) (radius k)) atTop
      (𝓝 (-I*((q^(2*n) : ℝ) : ℂ))) := by
  simpa only [div_one] using family_even_limit j n q 1 hq zero_lt_one

theorem te_odd_limit (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun k : ℕ => gamma (2*j+1) (te q hq n) (radius k)) atTop
      (𝓝 (-I*((q^(-(2*n : ℤ)) : ℝ) : ℂ))) := by
  simpa only [one_div,zpow_neg,zpow_natCast,inv_pow] using family_odd_limit j n q 1 hq zero_lt_one

theorem tm_even_limit (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun k : ℕ => gamma (2*j) (tm q hq n) (radius k)) atTop
      (𝓝 (-I*((q^(-(2*n : ℤ)) : ℝ) : ℂ))) := by
  have he : q/q^2 = q⁻¹ := by field_simp; ring
  simpa only [he,zpow_neg,zpow_natCast,inv_pow] using family_even_limit j n q (q^2) hq (sq_pos_of_pos hq)

theorem tm_odd_limit (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun k : ℕ => gamma (2*j+1) (tm q hq n) (radius k)) atTop
      (𝓝 (-I*((q^(2*n) : ℝ) : ℂ))) := by
  have he : q^2/q = q := by field_simp; ring
  simpa only [he] using family_odd_limit j n q (q^2) hq (sq_pos_of_pos hq)

end OQ14.RadialPairedFamily

#print axioms OQ14.RadialPairedFamily.family_chain
#print axioms OQ14.RadialPairedFamily.outer_le_double
#print axioms OQ14.RadialPairedFamily.width_bound
#print axioms OQ14.RadialPairedFamily.eventually_literal
#print axioms OQ14.RadialPairedFamily.layers_parameters
#print axioms OQ14.RadialPairedFamily.family_parameters
#print axioms OQ14.RadialPairedFamily.pair_width
#print axioms OQ14.RadialPairedFamily.pairs_parameters
#print axioms OQ14.RadialPairedFamily.paired_family_parameters
#print axioms OQ14.RadialPairedFamily.family_gamma_limit
#print axioms OQ14.RadialPairedFamily.family_even_limit
#print axioms OQ14.RadialPairedFamily.family_odd_limit
#print axioms OQ14.RadialPairedFamily.te_even_limit
#print axioms OQ14.RadialPairedFamily.te_odd_limit
#print axioms OQ14.RadialPairedFamily.tm_even_limit
#print axioms OQ14.RadialPairedFamily.tm_odd_limit
