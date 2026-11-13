import SimplePoleResidueForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! A one-dimensional kernel with a nonzero crossing excludes higher poles
of a genuinely meromorphic operator inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PoleOrder
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem inverse_order_negative (A : ℂ → H →L[ℂ] H) (z0 : ℂ)
    (hA : ContinuousAt A z0)
    (hm : MeromorphicAt (fun z => Ring.inverse (A z)) z0)
    (hu : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (hnot : ¬IsUnit (A z0)) : hm.order < 0 := by
  by_contra hn
  obtain ⟨C,hC⟩ := hm.tendsto_nhds_of_order_nonneg (le_of_not_gt hn)
  have ht := hA.tendsto.mono_left (show 𝓝[≠] z0 ≤ 𝓝 z0 from nhdsWithin_le_nhds)
  have hl : A z0*C = 1 := by
    apply tendsto_nhds_unique (ht.mul hC)
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with z hz
    exact (Ring.mul_inverse_cancel (A z) hz).symm
  have hr : C*A z0 = 1 := by
    apply tendsto_nhds_unique (hC.mul ht)
    apply tendsto_const_nhds.congr'
    filter_upwards [hu] with z hz
    exact (Ring.inverse_mul_cancel (A z) hz).symm
  exact hnot ⟨⟨A z0,C,hl,hr⟩,rfl⟩

theorem higher_pole_impossible (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ)
    (hA : HasDerivAt A A1 z0) (u : H) (φ : H →L[ℂ] ℂ)
    (hker : ∀ v, A z0 v = 0 → ∃ a : ℂ, v = a • u)
    (hφ : ∀ v, φ (A z0 v) = 0) (hd : φ (A1 u) ≠ 0)
    (hu : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (m : ℕ) (hm : 2 ≤ m)
    (G : ℂ → H →L[ℂ] H) (hG : AnalyticAt ℂ G z0) (hG0 : G z0 ≠ 0)
    (he : ∀ᶠ z in 𝓝[≠] z0, Ring.inverse (A z) = ((z-z0)^m)⁻¹ • G z) : False := by
  have hp : ∀ᶠ z in 𝓝[≠] z0, A z * G z = (z-z0)^m • (1 : H →L[ℂ] H) := by
    filter_upwards [he,hu,self_mem_nhdsWithin] with z he hu hz
    have hn : (z-z0)^m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hg : G z = (z-z0)^m • Ring.inverse (A z) := by
      rw [he, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [hg, mul_smul_comm, Ring.mul_inverse_cancel _ hu]
  have hprod : HasDerivAt (fun z => A z * G z)
      (A1 * G z0 + A z0 * deriv G z0) z0 :=
    hA.mul hG.differentiableAt.hasDerivAt
  have hpower : HasDerivAt (fun z : ℂ => (z-z0)^m • (1 : H →L[ℂ] H)) 0 z0 := by
    have hbase : HasDerivAt (fun z : ℂ => z-z0) (1 : ℂ) z0 := (hasDerivAt_id z0).sub_const z0
    have h := (hbase.pow m).smul_const (1 : H →L[ℂ] H)
    simpa only [sub_self, zero_pow (show m-1 ≠ 0 by omega), mul_zero, zero_mul, zero_smul] using h
  have hcenter : A z0 * G z0 = 0 := by
    have hlim := hpower.continuousAt.tendsto.mono_left
      (show 𝓝[≠] z0 ≤ 𝓝 z0 from nhdsWithin_le_nhds)
    have hlim' : Tendsto (fun z => A z * G z) (𝓝[≠] z0) (𝓝 0) := by
      have h0 : (z0-z0)^m • (1 : H →L[ℂ] H) = 0 := by
        simp only [sub_self, zero_pow (show m ≠ 0 by omega), zero_smul]
      rw [h0] at hlim
      exact hlim.congr' (hp.mono fun _ h => h.symm)
    exact tendsto_nhds_unique (hprod.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim'
  have hcenter' : A z0 * G z0 = (z0-z0)^m • (1 : H →L[ℂ] H) := by
    simp only [hcenter, sub_self, zero_pow (show m ≠ 0 by omega), zero_smul]
  have hall := eventuallyEq_nhds_of_eventuallyEq_nhdsNE hp hcenter'
  have hdprod : A1 * G z0 + A z0 * deriv G z0 = 0 :=
    hprod.unique (hpower.congr_of_eventuallyEq hall)
  apply hG0
  apply ContinuousLinearMap.ext
  intro x
  have hk : A z0 (G z0 x) = 0 := congrArg (fun L : H →L[ℂ] H => L x) hcenter
  obtain ⟨a,ha⟩ := hker _ hk
  have hh := congrArg (fun L : H →L[ℂ] H => φ (L x)) hdprod
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.zero_apply, map_add, hφ, add_zero, map_zero, ha,
    map_smul, smul_eq_mul] at hh
  have ha0 : a = 0 := (mul_eq_zero.mp hh).resolve_right hd
  simp only [ha, ha0, zero_smul, ContinuousLinearMap.zero_apply]

theorem inverse_order_eq_neg_one (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ)
    (hA : HasDerivAt A A1 z0) (u : H) (φ : H →L[ℂ] ℂ)
    (hker : ∀ v, A z0 v = 0 → ∃ a : ℂ, v = a • u)
    (hφ : ∀ v, φ (A z0 v) = 0) (hd : φ (A1 u) ≠ 0)
    (hm : MeromorphicAt (fun z => Ring.inverse (A z)) z0)
    (hu : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (hnot : ¬IsUnit (A z0)) :
    hm.order = (-1 : ℤ) := by
  have hneg := inverse_order_negative A z0 hA.continuousAt hm hu hnot
  obtain ⟨q,hq⟩ := WithTop.ne_top_iff_exists.mp hneg.ne_top
  have hqneg : q < 0 := by
    rw [← hq] at hneg
    exact_mod_cast hneg
  obtain ⟨G,hG,hG0,he⟩ := hm.order_eq_int_iff.mp hq.symm
  let m : ℕ := (-q).toNat
  have hqm : q = -(m : ℤ) := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hmpos : 0 < m := by omega
  have he' : ∀ᶠ z in 𝓝[≠] z0, Ring.inverse (A z) = ((z-z0)^m)⁻¹ • G z := by
    filter_upwards [he] with z hz
    simpa only [hqm, zpow_neg, zpow_natCast] using hz
  have hmone : m = 1 := by
    by_contra hn
    exact higher_pole_impossible A A1 z0 hA u φ hker hφ hd hu m (by omega) G hG hG0 he'
  rw [← hq, hqm, hmone]
  norm_num

end OQ14.Packet06PoleOrder
#print axioms OQ14.Packet06PoleOrder.inverse_order_negative
#print axioms OQ14.Packet06PoleOrder.higher_pole_impossible
#print axioms OQ14.Packet06PoleOrder.inverse_order_eq_neg_one
