import ConicalNormalizedInputCoefficient

/-! Intrinsic singular coefficients are determined by the actual local electric field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.ConicalIntrinsicCoefficient
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
  OQ14.ConicalRadialParticular OQ14.ConicalGraphProjection OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

def coefficient {p : Data} {b : ℝ} (s : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1) : ℂ :=
  Classical.choose (ConicalLocalExpansion.actual_projected_expansion s hb hai hν)

theorem coefficient_spec {p : Data} {b : ℝ} (s : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1) :
    projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      coefficient s hb hai hν*power p.exponent r+particular p.exponent (radialCorrection s) (tangentCorrection s) r :=
  Classical.choose_spec (ConicalLocalExpansion.actual_projected_expansion s hb hai hν)

theorem coefficient_unique {p : Data} {b : ℝ} (s : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1) (q : ℂ)
    (hq : projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      q*power p.exponent r+particular p.exponent (radialCorrection s) (tangentCorrection s) r) :
    q=coefficient s hb hai hν := by
  simpa only [one_mul] using ConicalNormalizedInputCoefficient.coefficient_scaled p b hb hν s s 1
    (fun i => by filter_upwards with x hx; simp only [one_mul])
    (coefficient s hb hai hν) q (coefficient_spec s hb hai hν) hq

theorem coefficient_scaled {p : Data} {b : ℝ} (s t : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1) (z : ℂ)
    (htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate t i x=z*totalCoordinate s i x) :
    coefficient t hb hai hν=z*coefficient s hb hai hν :=
  ConicalNormalizedInputCoefficient.coefficient_scaled p b hb hν s t z htot _ _
    (coefficient_spec s hb hai hν) (coefficient_spec t hb hai hν)

def totalProjected {p : Data} {b : ℝ} (s : System p b) (r : ℝ) : ℂ :=
  (r : ℂ)/(p.eigenvalue : ℂ)*ConicalLocalFlux.tangentTotal s r

def remainder {p : Data} {b : ℝ} (s : System p b) (r : ℝ) : ℂ :=
  particular p.exponent (radialCorrection s) (tangentCorrection s) r+
    (r : ℂ)/(p.eigenvalue : ℂ)*tangentCorrection s r

theorem remainder_continuous {p : Data} {b : ℝ} (s : System p b) (hν : p.exponent < 1) :
    ContinuousOn (remainder s) (Ioo (0 : ℝ) b) := by
  intro r hr
  exact (((particular_hasDerivAt p.exponent ⟨p.exponent_pos,hν⟩ _ _
    (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn r hr.1).continuousAt).add
      ((Complex.continuous_ofReal.continuousAt.div_const _).mul (tangentCorrection_continuous s).continuousAt)).continuousWithinAt

theorem remainder_bound {p : Data} {b : ℝ} (s : System p b) (hν : p.exponent < 1) :
    ∃ C : ℝ, ∀ r ∈ Ioo (0 : ℝ) b, ‖remainder s r‖ ≤ C*r := by
  obtain ⟨L,hL⟩ := ConicalNormalizedInputCoefficient.particular_bound p b hν s b
  obtain ⟨Ct,hCt⟩ := ConicalNormalizedInputCoefficient.tangent_bound p b s b
  refine ⟨L+Ct/p.eigenvalue,?_⟩
  intro r hr
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hr.1,abs_of_pos (eigenvalue_pos p)]
  exact (add_le_add (hL r hr)
    (mul_le_mul_of_nonneg_left (hCt r ⟨hr.1.le,hr.2.le⟩) (div_nonneg hr.1.le (eigenvalue_pos p).le))).trans_eq (by ring)

theorem total_expansion {p : Data} {b : ℝ} (s : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1) :
    totalProjected s =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      coefficient s hb hai hν*power p.exponent r+remainder s r := by
  filter_upwards [coefficient_spec s hb hai hν,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self (ConicalLocalFlux.tangentTotal_ae s)] with r he ht
  change _=coefficient s hb hai hν*power p.exponent r+
    (particular p.exponent (radialCorrection s) (tangentCorrection s) r+
      (r : ℂ)/(p.eigenvalue : ℂ)*tangentCorrection s r)
  simp only [totalProjected,projected,ht] at *
  linear_combination he

theorem tangentTotal_add {p : Data} {b : ℝ} (s t u : System p b)
    (htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate u i x=totalCoordinate s i x+totalCoordinate t i x) :
    ConicalLocalFlux.tangentTotal u =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      ConicalLocalFlux.tangentTotal s r+ConicalLocalFlux.tangentTotal t r := by
  have hi (i : Fin 3) : moment (totalCoordinate u i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
        moment (totalCoordinate s i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r+
        moment (totalCoordinate t i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r := by
    obtain ⟨C,hC,hbound⟩ := ConicalMomentWeights.tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    have hσ : MemLp (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) 2 AngularPower.angularMeasure :=
      MemLp.of_bound (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i).aestronglyMeasurable C
        (Filter.Eventually.of_forall hbound)
    have hp := PolarMomentAE.polar_ae (htot i)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hp,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self (PolarMomentEnergy.slice_memLp_ae (totalCoordinate s i)),
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self (PolarMomentEnergy.slice_memLp_ae (totalCoordinate t i)),
      ae_restrict_mem measurableSet_Ioo] with r hr hs ht hm
    unfold moment
    have hInt := integral_add (hs.integrable_mul hσ) (ht.integrable_mul hσ)
    simp only [Pi.mul_apply] at hInt
    rw [←hInt]
    apply integral_congr_ae
    filter_upwards [hr] with n hn
    have hx : r • (n : Space) ∈ ball (0 : Space) b := by
      simpa only [mem_ball,dist_zero_right,norm_smul,AngularPower.sphere_norm,Real.norm_eq_abs,abs_of_pos hm.1,mul_one] using hm.2
    rw [hn hx]
    ring
  filter_upwards [ae_all_iff.mpr hi] with r hr
  simp only [ConicalLocalFlux.tangentTotal,hr,Finset.sum_add_distrib]

theorem coefficient_add {p : Data} {b : ℝ} (s t u : System p b) (hb : 0 < b)
    (hai : b < p.cutoff.rIn) (hν : p.exponent < 1)
    (htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate u i x=totalCoordinate s i x+totalCoordinate t i x) :
    coefficient u hb hai hν=coefficient s hb hai hν+coefficient t hb hai hν := by
  by_contra hne
  let q := coefficient u hb hai hν-(coefficient s hb hai hν+coefficient t hb hai hν)
  have hq : q≠0 := sub_ne_zero.mpr hne
  obtain ⟨Cs,hCs⟩ := remainder_bound s hν
  obtain ⟨Ct,hCt⟩ := remainder_bound t hν
  obtain ⟨Cu,hCu⟩ := remainder_bound u hν
  apply ConicalRadialUnbounded.nonzero_power_not_linear_bounded p.exponent b ⟨p.exponent_pos,hν⟩ hb q hq
    (fun r => remainder u r-(remainder s r+remainder t r))
    (fun r hr => ((remainder_continuous u hν r hr).sub
      ((remainder_continuous s hν r hr).add (remainder_continuous t hν r hr))))
    (Cu+(Cs+Ct))
  · intro r hr
    exact (norm_sub_le _ _).trans ((add_le_add (hCu r hr)
      ((norm_add_le _ _).trans (add_le_add (hCs r hr) (hCt r hr)))).trans_eq (by ring))
  · refine ⟨0,?_⟩
    filter_upwards [total_expansion s hb hai hν,total_expansion t hb hai hν,total_expansion u hb hai hν,
      tangentTotal_add s t u htot] with r hs ht hu hT
    have hsum : totalProjected u r=totalProjected s r+totalProjected t r := by
      simp only [totalProjected,hT,mul_add]
    have he : q*power p.exponent r+(remainder u r-(remainder s r+remainder t r))=0 := by
      dsimp only [q]
      rw [hs,ht,hu] at hsum
      linear_combination hsum
    simp only [he,norm_zero,zero_mul,le_refl]

end OQ14.ConicalIntrinsicCoefficient
#print axioms OQ14.ConicalIntrinsicCoefficient.coefficient_spec
#print axioms OQ14.ConicalIntrinsicCoefficient.coefficient_unique
#print axioms OQ14.ConicalIntrinsicCoefficient.coefficient_scaled
#print axioms OQ14.ConicalIntrinsicCoefficient.remainder_continuous
#print axioms OQ14.ConicalIntrinsicCoefficient.remainder_bound
#print axioms OQ14.ConicalIntrinsicCoefficient.total_expansion
#print axioms OQ14.ConicalIntrinsicCoefficient.tangentTotal_add
#print axioms OQ14.ConicalIntrinsicCoefficient.coefficient_add
