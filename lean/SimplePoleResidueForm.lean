import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.Banach

/-! Form of the residue of the inverse of an analytic operator family at a simple pole: if the
kernel at the pole is spanned by `u`, the covector `φ` kills the range, and `φ (A' u) ≠ 0`, then any
operator-norm residue limit equals `x ↦ (φ x / φ (A' u)) • u`. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SimplePoleResidueForm
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem residue_kills_kernel (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ) (hA : HasDerivAt A A1 z0)
    (hinv : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (R : H →L[ℂ] H)
    (hR : Tendsto (fun z => (z-z0) • Ring.inverse (A z)) (𝓝[≠] z0) (𝓝 R)) :
    A z0 * R=0 := by
  have hc : Tendsto A (𝓝[≠] z0) (𝓝 (A z0)) := hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun z => A z * ((z-z0) • Ring.inverse (A z))) (𝓝[≠] z0) (𝓝 (A z0 * R)) := hc.mul hR
  have h2 : Tendsto (fun z : ℂ => A z * ((z-z0) • Ring.inverse (A z))) (𝓝[≠] z0) (𝓝 0) := by
    have hz : Tendsto (fun z : ℂ => z-z0) (𝓝[≠] z0) (𝓝 0) := by
      have h0 : Tendsto (fun z : ℂ => z-z0) (𝓝 z0) (𝓝 0) := by
        have := (continuous_id.sub (continuous_const (y := z0))).tendsto z0
        simpa using this
      exact h0.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun z : ℂ => (z-z0) • (1 : H →L[ℂ] H)) (𝓝[≠] z0) (𝓝 0) := by
      simpa using hz.smul_const (1 : H →L[ℂ] H)
    refine h3.congr' ?_
    filter_upwards [hinv] with z hz
    rw [mul_smul_comm,Ring.mul_inverse_cancel _ hz]
  exact tendsto_nhds_unique h1 h2

theorem residue_form (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ) (hA : HasDerivAt A A1 z0)
    (u : H) (φ : H →L[ℂ] ℂ)
    (hker : ∀ v, A z0 v=0 → ∃ a : ℂ,v=a • u)
    (hφ : ∀ v, φ (A z0 v)=0) (hd : φ (A1 u)≠0)
    (hinv : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (R : H →L[ℂ] H)
    (hR : Tendsto (fun z => (z-z0) • Ring.inverse (A z)) (𝓝[≠] z0) (𝓝 R)) :
    ∀ x, R x=(φ x/φ (A1 u)) • u := by
  intro x
  have hk : A z0 (R x)=0 := by
    have := residue_kills_kernel A A1 z0 hA hinv R hR
    exact congrArg (fun T : H →L[ℂ] H => T x) this
  obtain ⟨a,ha⟩ := hker _ hk
  have hs : Tendsto (slope A z0) (𝓝[≠] z0) (𝓝 A1) := hasDerivAt_iff_tendsto_slope.mp hA
  have hlim : Tendsto (fun z => φ ((slope A z0 z * ((z-z0) • Ring.inverse (A z))) x)) (𝓝[≠] z0)
      (𝓝 (φ ((A1 * R) x))) := by
    have h := hs.mul hR
    exact φ.continuous.continuousAt.tendsto.comp
      ((ContinuousLinearMap.apply ℂ H x).continuous.continuousAt.tendsto.comp h)
  have heq : ∀ᶠ z in 𝓝[≠] z0, φ ((slope A z0 z * ((z-z0) • Ring.inverse (A z))) x)=φ x := by
    filter_upwards [hinv,self_mem_nhdsWithin] with z hz hne
    have hne' : z-z0≠0 := sub_ne_zero.mpr hne
    have h1 : (A z) (((z-z0) • Ring.inverse (A z)) x)=(z-z0) • x := by
      have := congrArg (fun T : H →L[ℂ] H => T x) (Ring.mul_inverse_cancel _ hz)
      simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] at this
      simp only [ContinuousLinearMap.smul_apply,map_smul,this]
    have h2 : slope A z0 z=(z-z0)⁻¹ • (A z-A z0) := by simp [slope_def_module]
    set y := ((z-z0) • Ring.inverse (A z)) x with hy
    have h3 : (slope A z0 z) y=(z-z0)⁻¹ • ((A z) y-(A z0) y) := by
      rw [h2]; simp
    have h4 : φ ((slope A z0 z) y)=φ x := by
      rw [h3,map_smul,map_sub,hφ,h1]
      simp [map_smul, hne']
    rw [ContinuousLinearMap.mul_apply]
    exact h4
  have hconst : Tendsto (fun z : ℂ => φ x) (𝓝[≠] z0) (𝓝 (φ x)) := tendsto_const_nhds
  have hxe : φ ((A1 * R) x)=φ x :=
    tendsto_nhds_unique hlim (hconst.congr' (heq.mono fun z hz => hz.symm))
  rw [ContinuousLinearMap.mul_apply,ha,map_smul,map_smul,smul_eq_mul] at hxe
  rw [ha]
  congr 1
  field_simp
  exact hxe

end OQ14.SimplePoleResidueForm
#print axioms OQ14.SimplePoleResidueForm.residue_kills_kernel
#print axioms OQ14.SimplePoleResidueForm.residue_form
