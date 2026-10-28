import ComplexDyadicMomentFar
import AnnularMomentClassical
import RadialBoundarySelection
import ExteriorHelmholtz
import AnnularMomentEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RealDyadicMomentOutgoing
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.SphericalMomentEquation OQ14.RadialMoment OQ14.RadialMomentClassical
  OQ14.RadialMomentODE OQ14.RadialRellich OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
open scoped Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem field_ofReal (c : Coefficient) (k : ℝ) (u : VectorL2) :
    ComplexExteriorIntegral.field c k u = ExteriorContinuity.electric k (DynamicVolume.source c u) := by
  funext x i
  simp only [ComplexExteriorIntegral.field, ExteriorContinuity.electric, KernelConvolution.response,
    ComplexDynamicKernel.dyadic_ofReal]

theorem outgoing_moment (c : Coefficient) (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorL2) (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0) (i : Fin 3) :
    ∃ a : ℂ, ∀ r, R < r →
      (r : ℂ) * RadialMoment.moment (fun x => ComplexExteriorIntegral.field c k u x i)
        (angularPolynomial p) r = a * outgoing l k r := by
  let v : Space → ℂ := fun x => ExteriorContinuity.electric k (DynamicVolume.source c u) x i
  let P := angularPolynomial p
  let U := RadialMoment.moment v P
  let F := radialFlux (momentD v P)
  have hρ := DynamicVolume.source_integrable c u R hc
  have hzero := DynamicVolume.source_zero c u R hc
  have hu (L : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) v (AnnularMoment.annulus R L) := by
    intro x hx
    exact ((contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt k (DynamicVolume.source c u) hρ R hzero x hx.1)) i).contDiffWithinAt
  have heq (L : ℝ) : ∀ x, x ∈ AnnularMoment.annulus R L → laplacian v x + (k : ℂ)^2 * v x = 0 := by
    intro x hx
    exact (ExteriorHelmholtz.exterior_helmholtz k hk.ne' (DynamicVolume.source c u) hρ R hzero x hx.1).1 i
  have hclass (r : ℝ) (hr : R < r) := AnnularMomentClassical.moment_classical_of_weak l (k : ℂ) R (r+1) hR v
    (hu (r+1)) P (angularPolynomial_continuous p)
    (fun η hη hηc hηs => by
      simpa only [RadialMomentWeights.coefficientA, RadialMomentWeights.coefficientB, RadialMomentWeights.coefficientC] using
        AnnularMomentEquation.weak_radial_real_test R (r+1) hR k v (hu (r+1)) (heq (r+1)) p l hp hh η hη hηc hηs) r ⟨hr, by linarith⟩
  have hU (r : ℝ) (hr : R < r) : HasDerivAt U (F r/(r : ℂ)^2) r := by
    rw [← (hclass r hr).2.2]
    exact AnnularMoment.moment_hasDerivAt R (r+1) r hR ⟨hr, by linarith⟩ v (hu (r+1)) P (angularPolynomial_continuous p)
  have hF (r : ℝ) (hr : R < r) : HasDerivAt F
      (((l : ℂ)*(l+1)-(k : ℂ)^2*(r : ℂ)^2)*U r) r := (hclass r hr).2.1
  have hlimit := ComplexDyadicMomentFar.scaled_moment_limit c (k : ℂ) R hR u hc p i
  rw [field_ofReal] at hlimit
  have hlim : Tendsto (fun r => phase k r * riccati U r) atTop
      (𝓝 (ComplexDyadicMomentFar.momentAmplitude c k u p i)) := by
    convert hlimit using 1
    funext r
    simp only [phase, riccati, ComplexDyadicMomentFar.scale, U, v, P]
    ring
  obtain ⟨a, ha, _⟩ := RadialBoundarySelection.ode_outgoing_selection l k hk R hR (riccati U) (riccatiD U F)
    (fun r hr => riccati_hasDerivAt U F r (ne_of_gt (lt_of_le_of_lt hR hr)) (hU r hr))
    (fun r hr => riccatiD_hasDerivAt l (k : ℂ) U F r (ne_of_gt (lt_of_le_of_lt hR hr)) (hU r hr) (hF r hr)) _ hlim
  refine ⟨a, ?_⟩
  intro r hr
  rw [field_ofReal]
  exact ha r hr

#print axioms OQ14.RealDyadicMomentOutgoing.field_ofReal
#print axioms OQ14.RealDyadicMomentOutgoing.outgoing_moment
end OQ14.RealDyadicMomentOutgoing
