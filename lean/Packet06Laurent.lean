import Packet06PoleOrder
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! An actual simple meromorphic inverse has an analytic regular part and the
reciprocal rank-one residue fixed by its crossing pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06Laurent
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem analytic_dslope (G : ℂ → H →L[ℂ] H) (z0 : ℂ) (hG : AnalyticAt ℂ G z0) :
    AnalyticAt ℂ (dslope G z0) z0 := by
  obtain ⟨p,hp⟩ := hG
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

theorem simple_inverse_expansion (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ)
    (hA : HasDerivAt A A1 z0) (u : H) (φ : H →L[ℂ] ℂ)
    (hker : ∀ v, A z0 v = 0 → ∃ a : ℂ, v = a • u)
    (hφ : ∀ v, φ (A z0 v) = 0) (hd : φ (A1 u) ≠ 0)
    (hm : MeromorphicAt (fun z => Ring.inverse (A z)) z0)
    (hu : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (hnot : ¬IsUnit (A z0)) :
    ∃ (R : H →L[ℂ] H) (B : ℂ → H →L[ℂ] H),
      R ≠ 0 ∧ AnalyticAt ℂ B z0 ∧
      (∀ x, R x = (φ x / φ (A1 u)) • u) ∧
      Tendsto (fun z => (z-z0) • Ring.inverse (A z)) (𝓝[≠] z0) (𝓝 R) ∧
      (∀ᶠ z in 𝓝[≠] z0, Ring.inverse (A z) = (z-z0)⁻¹ • R + B z) := by
  have ho := Packet06PoleOrder.inverse_order_eq_neg_one A A1 z0 hA u φ hker hφ hd hm hu hnot
  obtain ⟨G,hG,hG0,he⟩ := hm.order_eq_int_iff.mp ho
  have he' : ∀ᶠ z in 𝓝[≠] z0, Ring.inverse (A z) = (z-z0)⁻¹ • G z := by
    filter_upwards [he] with z hz
    simpa only [zpow_neg_one] using hz
  have hlim : Tendsto (fun z => (z-z0) • Ring.inverse (A z)) (𝓝[≠] z0) (𝓝 (G z0)) := by
    apply (hG.continuousAt.tendsto.mono_left (show 𝓝[≠] z0 ≤ 𝓝 z0 from nhdsWithin_le_nhds)).congr'
    filter_upwards [he',self_mem_nhdsWithin] with z hz hne
    rw [hz,smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr hne),one_smul]
  refine ⟨G z0,dslope G z0,hG0,analytic_dslope G z0 hG,
    SimplePoleResidueForm.residue_form A A1 z0 hA u φ hker hφ hd hu (G z0) hlim,hlim,?_⟩
  filter_upwards [he',self_mem_nhdsWithin] with z hz hne
  rw [hz,dslope_of_ne _ hne,slope_def_module,smul_sub]
  abel

end OQ14.Packet06Laurent
#print axioms OQ14.Packet06Laurent.analytic_dslope
#print axioms OQ14.Packet06Laurent.simple_inverse_expansion
