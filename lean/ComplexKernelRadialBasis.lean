import WeakAnnularBasis
import ComplexSphereHelmholtz
import ComplexExteriorHelmholtz

/-! Actual interior and exterior complex response moments have Riccati expansions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexKernelRadialBasis
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakHelmholtzRegularity
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem weak_congr_ae (k : ℂ) (Ω : Set Space) (f g : Space → ℂ)
    (hfg : f =ᵐ[volume] g) (hg : IsWeakHelmholtz k Ω g) : IsWeakHelmholtz k Ω f := by
  intro φ hφ hc hs
  calc
    (∫ x, f x * (ExteriorHelmholtz.laplacian φ x + k^2 * φ x)) =
        ∫ x, g x * (ExteriorHelmholtz.laplacian φ x + k^2 * φ x) :=
      integral_congr_ae (hfg.mono (fun x hx => by dsimp only; rw [hx]))
    _ = 0 := hg φ hφ hc hs

theorem interior_coordinate (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) :
    IsWeakHelmholtz (z*n) (AnnularMoment.annulus 0 1)
      (NewtonL2.physicalCoordinate (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i) := by
  have hw := weak_congr_ae (z*n) (ball 0 1) _ _
    (NewtonL2.physicalCoordinate_ae (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i)
    (ComplexSphereHelmholtz.actual_weak_helmholtz n hn z hz u hker i)
  intro φ hφ hc hs
  exact hw φ hφ hc (hs.trans (fun x hx => by simpa only [mem_ball, dist_zero_right] using hx.2))

/-- Every actual sphere kernel vector has the two interior radial modes in every harmonic component. -/
theorem interior_moment_expansion (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c d : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u) i)
        (SphericalMomentEquation.angularPolynomial p) r =
      c * RadialRellich.outgoing l (z*n) r + d * RadialRellich.incoming l (z*n) r := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact WeakAnnularBasis.moment_expansion 0 1 a b (by norm_num) ha hb (z*n) (mul_ne_zero hz hn0) _
    (interior_coordinate n hn z hz u hker i) p l hp hh

theorem exterior_coordinate (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2) (i : Fin 3) :
    IsWeakHelmholtz z (AnnularMoment.annulus 1 T)
      (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i) := by
  have hw := weak_congr_ae z ((ball 0 T) \ (closedBall 0 1)) _ _
    (NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)
    (ComplexExteriorHelmholtz.actual_weak_helmholtz n hn z hz T hT u i)
  intro φ hφ hc hs
  apply hw φ hφ hc (hs.trans ?_)
  intro x hx
  refine ⟨?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using hx.2
  · simpa only [mem_closedBall, dist_zero_right, not_le] using hx.1

/-- The actual outgoing-source response has an exterior two-mode expansion; selecting the outgoing coefficient is separate. -/
theorem exterior_moment_expansion (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2) (i : Fin 3)
    (a b : ℝ) (ha : 1 < a) (hb : b < T)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c d : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Icc a b),
      (r : ℂ) * RadialMoment.moment
        (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i)
        (SphericalMomentEquation.angularPolynomial p) r =
      c * RadialRellich.outgoing l z r + d * RadialRellich.incoming l z r :=
  WeakAnnularBasis.moment_expansion 1 T a b (by norm_num) ha hb z hz _
    (exterior_coordinate n hn z hz T hT u i) p l hp hh

end OQ14.ComplexKernelRadialBasis
#print axioms OQ14.ComplexKernelRadialBasis.interior_coordinate
#print axioms OQ14.ComplexKernelRadialBasis.interior_moment_expansion
#print axioms OQ14.ComplexKernelRadialBasis.exterior_coordinate
#print axioms OQ14.ComplexKernelRadialBasis.exterior_moment_expansion
