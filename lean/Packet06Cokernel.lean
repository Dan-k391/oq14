import Packet06SectorCrossing

/-! Algebraic cokernel bridge from the constant Laurent coefficient.
The identities are explicit hypotheses here; actual field instantiation must
supply them from the proved meromorphic inverse expansion. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06Cokernel
open Complex Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A Laurent coefficient identity and a rank-one residue identify the actual
operator range with the kernel of the left functional. -/
theorem range_eq_kernel (A A₁ G R : E →L[ℂ] E) (φ : E →L[ℂ] ℂ)
    (u : E) (d : ℂ)
    (hann : ∀ x, φ (A x) = 0)
    (hres : ∀ x, R x = (φ x / d) • u)
    (hconstant : A.comp G + A₁.comp R = 1) :
    LinearMap.range A.toLinearMap = LinearMap.ker φ.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact hann x
  · intro hy
    change φ y = 0 at hy
    refine ⟨G y, ?_⟩
    have h := congrArg (fun L : E →L[ℂ] E => L y) hconstant
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply, hres y, hy, zero_div, zero_smul, map_zero, add_zero] at h
    exact h

theorem range_closed (A A₁ G R : E →L[ℂ] E) (φ : E →L[ℂ] ℂ)
    (u : E) (d : ℂ)
    (hann : ∀ x, φ (A x) = 0)
    (hres : ∀ x, R x = (φ x / d) • u)
    (hconstant : A.comp G + A₁.comp R = 1) :
    IsClosed (Set.range A) := by
  change IsClosed (LinearMap.range A.toLinearMap : Set E)
  rw [range_eq_kernel A A₁ G R φ u d hann hres hconstant]
  exact ContinuousLinearMap.isClosed_ker φ

theorem quotient_finrank_one (A A₁ G R : E →L[ℂ] E) (φ : E →L[ℂ] ℂ)
    (u : E) (d : ℂ)
    (hann : ∀ x, φ (A x) = 0)
    (hres : ∀ x, R x = (φ x / d) • u)
    (hconstant : A.comp G + A₁.comp R = 1)
    (v : E) (hv : φ v ≠ 0) :
    Module.finrank ℂ (E ⧸ LinearMap.range A.toLinearMap) = 1 := by
  rw [range_eq_kernel A A₁ G R φ u d hann hres hconstant]
  have hsurj : Function.Surjective φ.toLinearMap := by
    intro c
    refine ⟨(c / φ v) • v, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
    field_simp [hv]
  simpa only [Module.finrank_self] using (φ.toLinearMap.quotKerEquivOfSurjective hsurj).finrank_eq

/-- Differentiate the true punctured inverse identity after removing its
simple pole. This supplies the constant Laurent coefficient identity. -/
theorem laurent_constant_identity (A : ℂ → E →L[ℂ] E) (A₁ : E →L[ℂ] E)
    (z₀ : ℂ) (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E)
    (hA : HasDerivAt A A₁ z₀) (hB : AnalyticAt ℂ B z₀)
    (hu : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (A z))
    (hexp : ∀ᶠ z in 𝓝[≠] z₀, Ring.inverse (A z) = (z-z₀)⁻¹ • R + B z) :
    (A z₀).comp (B z₀) + A₁.comp R = 1 := by
  let G : ℂ → E →L[ℂ] E := fun z => R + (z-z₀) • B z
  have hG : HasDerivAt G (B z₀) z₀ := by
    have hx : HasDerivAt (fun z : ℂ => z-z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
    have hb := hB.differentiableAt.hasDerivAt
    have hh := (hasDerivAt_const z₀ R).add (hx.smul hb)
    simpa only [G, sub_self, one_smul, zero_smul, add_zero, zero_add] using hh
  have hprod : HasDerivAt (fun z => A z * G z)
      (A₁*R + A z₀*B z₀) z₀ := by
    have hh := hA.mul hG
    simpa only [G, sub_self, zero_smul, add_zero] using hh
  have hp : ∀ᶠ z in 𝓝[≠] z₀, A z * G z = (z-z₀) • (1 : E →L[ℂ] E) := by
    filter_upwards [hexp,hu,self_mem_nhdsWithin] with z he hz hne
    have hn : z-z₀ ≠ 0 := sub_ne_zero.mpr hne
    have hg : G z = (z-z₀) • Ring.inverse (A z) := by
      rw [he]
      simp only [G, smul_add, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [hg, mul_smul_comm, Ring.mul_inverse_cancel _ hz]
  have hlin : HasDerivAt (fun z : ℂ => (z-z₀) • (1 : E →L[ℂ] E)) 1 z₀ := by
    simpa using ((hasDerivAt_id z₀).sub_const z₀).smul_const (1 : E →L[ℂ] E)
  have hc : A z₀ * G z₀ = 0 := by
    have hlim : Filter.Tendsto (fun z : ℂ => (z-z₀) • (1 : E →L[ℂ] E))
        (𝓝[≠] z₀) (𝓝 0) := by
      simpa only [sub_self, zero_smul] using
        (hlin.continuousAt.tendsto.mono_left
          (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds))
    exact tendsto_nhds_unique (hprod.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hlim.congr' (hp.mono fun _ h => h.symm))
  have hc' : A z₀ * G z₀ = (z₀-z₀) • (1 : E →L[ℂ] E) := by simp [hc]
  have hall := eventuallyEq_nhds_of_eventuallyEq_nhdsNE hp hc'
  have hh := hprod.unique (hlin.congr_of_eventuallyEq hall)
  change A z₀ * B z₀ + A₁ * R = 1
  simpa only [add_comm] using hh

#print axioms OQ14.Packet06Cokernel.laurent_constant_identity

#print axioms OQ14.Packet06Cokernel.range_eq_kernel
#print axioms OQ14.Packet06Cokernel.range_closed
#print axioms OQ14.Packet06Cokernel.quotient_finrank_one
end OQ14.Packet06Cokernel
