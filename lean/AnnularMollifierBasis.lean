import AnnularRiccatiBasis
import HelmholtzMollifiers
import PolarMomentOperator

/-! Actual weak Helmholtz mollifiers, annular Riccati expansions, and strong radial convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.AnnularMollifierBasis
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.WeakHelmholtzRegularity OQ14.WeakPoynting OQ14.PolarMomentOperator
open scoped Topology

theorem reflected_support_annulus (R L a b ε : ℝ)
    (hlo : R + ε < a) (hhi : b + ε < L) (ρ : Space → ℂ)
    (hρ : tsupport ρ ⊆ closedBall 0 ε) (x : Space)
    (hx : x ∈ AnnularMoment.annulus a b) :
    tsupport (LocalHelmholtzRepresentation.reflect x ρ) ⊆ AnnularMoment.annulus R L := by
  intro y hy
  have he : ‖x-y‖ ≤ ε := by
    simpa only [mem_closedBall, dist_zero_right] using hρ (reflect_tsupport x ρ hy)
  have hxy : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-y) y
  have hyx : ‖y‖ ≤ ‖x-y‖ + ‖x‖ := by
    have h := norm_add_le (y-x) x
    simpa only [sub_add_cancel, norm_sub_rev] using h
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem eventually_classical (R L a b : ℝ) (ha : R < a) (hb : b < L)
    (k : ℂ) (u : PolarMomentEnergy.ScalarL2)
    (hw : IsWeakHelmholtz k (AnnularMoment.annulus R L) u) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ AnnularMoment.annulus a b,
      ExteriorHelmholtz.laplacian (smoothScalar (complexKernel (shrinkingBump n)) u) x +
        k^2 * smoothScalar (complexKernel (shrinkingBump n)) u x = 0 := by
  have hl := shrinkingBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr ha))
  have hh := shrinkingBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hb))
  filter_upwards [hl, hh] with n hnlo hnhi
  intro x hx
  apply smooth_helmholtz k (AnnularMoment.annulus R L) u (complexKernel (shrinkingBump n))
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hw
    (complexKernel_regular _) (complexKernel_compact _)
  apply reflected_support_annulus R L a b (shrinkingBump n).rOut
    (by linarith) (by linarith) _ _ x hx
  rw [HelmholtzMollifiers.complexKernel_tsupport]

theorem eventually_moment_expansion (R L a b : ℝ) (ha : R < a) (hb : b < L)
    (ha0 : 0 ≤ a) (k : ℂ) (hk : k ≠ 0) (u : PolarMomentEnergy.ScalarL2)
    (hw : IsWeakHelmholtz k (AnnularMoment.annulus R L) u)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ᶠ n : ℕ in atTop, ∃ c d : ℂ, ∀ r ∈ Ioo a b,
      (r : ℂ) * RadialMoment.moment (smoothScalar (complexKernel (shrinkingBump n)) u)
        (SphericalMomentEquation.angularPolynomial p) r =
      c * RadialRellich.outgoing l k r + d * RadialRellich.incoming l k r := by
  filter_upwards [eventually_classical R L a b ha hb k u hw] with n hn
  exact AnnularRiccatiBasis.helmholtz_moment_expansion a b ha0 k hk _
    (smoothScalar_regular (complexKernel_regular _) (complexKernel_compact _) u).contDiffOn
    hn p l hp hh

theorem radial_mollifiers_tendsto (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (u : PolarMomentEnergy.ScalarL2) :
    Tendsto (fun n : ℕ => operator σ hσm hσ (mollifyL2 (shrinkingBump n) u)) atTop
      (𝓝 (operator σ hσm hσ u)) :=
  (operator σ hσm hσ).continuous.continuousAt.tendsto.comp
    (mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto u)

theorem radial_mollifier_actual (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (u : PolarMomentEnergy.ScalarL2) (n : ℕ) :
    (operator σ hσm hσ (mollifyL2 (shrinkingBump n) u) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r =>
        (r : ℂ) * RadialMoment.moment (smoothScalar (complexKernel (shrinkingBump n)) u) σ r := by
  have he := PolarMomentAE.moment_congr (smoothScalar_memLp (shrinkingBump n) u).coeFn_toLp σ
  filter_upwards [operator_actual σ hσm hσ (mollifyL2 (shrinkingBump n) u), he] with r hr he
  change PolarMomentTesting.moment (mollifyL2 (shrinkingBump n) u) σ r =
    PolarMomentTesting.moment (smoothScalar (complexKernel (shrinkingBump n)) u) σ r at he
  rw [hr, he]
  rfl

end OQ14.AnnularMollifierBasis
#print axioms OQ14.AnnularMollifierBasis.reflected_support_annulus
#print axioms OQ14.AnnularMollifierBasis.eventually_classical
#print axioms OQ14.AnnularMollifierBasis.eventually_moment_expansion
#print axioms OQ14.AnnularMollifierBasis.radial_mollifiers_tendsto
#print axioms OQ14.AnnularMollifierBasis.radial_mollifier_actual
