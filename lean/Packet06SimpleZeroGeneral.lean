import Packet06SimpleZeroLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SimpleZero
open Filter Metric Set
open scoped Topology

theorem zeros_near_simple (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (haU : a ∈ U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hzero : f a = 0) (hder : deriv f a ≠ 0)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∃ z, dist z a < ε ∧ F n z = 0 := by
  let d := deriv f a
  let L : ℂ →L[ℂ] ℂ := d⁻¹ • 1
  have hconv' : TendstoLocallyUniformlyOn (fun n z => d⁻¹ * F n z)
      (fun z => d⁻¹ * f z) atTop U := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
    intro K hKU hK
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv K hKU hK
    have hh := L.uniformContinuous.comp_tendstoUniformlyOn h
    simpa only [Function.comp_def, L, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul] using hh
  have hf' : DifferentiableOn ℂ (fun z => d⁻¹ * f z) U := hf.const_mul _
  have hF' : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun z => d⁻¹ * F n z) U :=
    hF.mono (fun n hn => hn.const_mul _)
  have hd' : deriv (fun z => d⁻¹ * f z) a = 1 := by
    rw [deriv_const_mul _ ((hf a haU).differentiableAt (hU.mem_nhds haU))]
    exact inv_mul_cancel₀ hder
  intro ε hε
  have h := zeros_tend_to_simple_normalized U hU a haU (fun n z => d⁻¹ * F n z)
    (fun z => d⁻¹ * f z) hf' (by simp [hzero]) hd' hF' hconv' ε hε
  filter_upwards [h] with n hn
  obtain ⟨z,hz,hval⟩ := hn
  exact ⟨z,hz,(mul_eq_zero.mp hval).resolve_left (inv_ne_zero hder)⟩
theorem unique_simple_zeros_near (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (haU : a ∈ U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hzero : f a = 0) (hder : deriv f a ≠ 0)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    ∀ ε > 0, ∃ r > 0, r < ε ∧ ∀ᶠ n in atTop, ∃ z ∈ closedBall a r,
      F n z = 0 ∧ deriv (F n) z ≠ 0 ∧
      ∀ w ∈ closedBall a r, F n w = 0 → w = z := by
  let d := deriv f a
  let L : ℂ →L[ℂ] ℂ := d⁻¹ • 1
  have hconv' : TendstoLocallyUniformlyOn (fun n z => d⁻¹ * F n z)
      (fun z => d⁻¹ * f z) atTop U := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
    intro K hKU hK
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv K hKU hK
    have hh := L.uniformContinuous.comp_tendstoUniformlyOn h
    simpa only [Function.comp_def, L, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul] using hh
  have hf' : DifferentiableOn ℂ (fun z => d⁻¹ * f z) U := hf.const_mul _
  have hF' : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun z => d⁻¹ * F n z) U :=
    hF.mono (fun n hn => hn.const_mul _)
  have hd' : deriv (fun z => d⁻¹ * f z) a = 1 := by
    rw [deriv_const_mul _ ((hf a haU).differentiableAt (hU.mem_nhds haU))]
    exact inv_mul_cancel₀ hder
  intro ε hε
  obtain ⟨r, hr, hrε, h⟩ := unique_simple_zeros_normalized U hU a haU
    (fun n z => d⁻¹ * F n z) (fun z => d⁻¹ * f z)
    hf' (by simp [hzero]) hd' hF' hconv' ε hε
  refine ⟨r, hr, hrε, ?_⟩
  filter_upwards [h, hF] with n hn hFn
  obtain ⟨z,hz,hval,hzder,huniq⟩ := hn
  have hz0 : F n z = 0 := (mul_eq_zero.mp hval).resolve_left (inv_ne_zero hder)
  have hd0 : deriv (F n) z ≠ 0 := by
    intro hzder0
    have he := deriv_const_mul_field d⁻¹ (v := F n) (x := z)
    rw [hzder0, mul_zero] at he
    exact hzder he
  refine ⟨z,hz,hz0,hd0,?_⟩
  intro w hw hw0
  exact huniq w hw (by simp [hw0])
#print axioms OQ14.Packet06SimpleZero.unique_simple_zeros_near
#print axioms OQ14.Packet06SimpleZero.zeros_near_simple
end OQ14.Packet06SimpleZero
