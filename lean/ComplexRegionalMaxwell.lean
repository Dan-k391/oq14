import WeakAnnularMoment
import RegionalMaxwellHelmholtz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexRegionalMaxwell
open Complex MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorGreen
  OQ14.ExteriorHelmholtz OQ14.WeakHelmholtzRegularity
  OQ14.RegionalMaxwellHelmholtz OQ14.HarmonicPolynomial
  OQ14.SphericalMomentEquation OQ14.RadialMoment
open scoped Topology

def TestMaxwell (k ε : ℂ) (Ω : Set Space) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : Test Ω),
    curlPair (fieldPair E) i f = (I*k)*fieldPair H i f ∧
    curlPair (fieldPair H) i f = (-(I*k*ε))*fieldPair E i f

theorem electric_lapPair (k ε : ℂ) (hk : k ≠ 0) (hε : ε ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H) (i : Fin 3) (f : Test Ω) :
    lapPair (fieldPair E) i f+(k^2*ε)*fieldPair E i f = 0 := by
  have hb : -(I*k*ε) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero hk) hε)
  have h := pair_helmholtz (fieldPair E) (fieldPair H) (I*k) (-(I*k*ε)) hb
    (fun j g => (hM j g).1) (fun j g => (hM j g).2) i f
  convert h using 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

theorem electric_weak_helmholtz (k n : ℂ) (hk : k ≠ 0) (hn : n ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k (n^2) Ω E H)
    (hE : IntegrableTests Ω E) (i : Fin 3) :
    IsWeakHelmholtz (k*n) Ω (fun x => E x i) := by
  intro φ hφ hc hs
  let f : Test Ω := ⟨φ,hφ,hc,hs⟩
  change (∫ x, E x i*(laplacian f.val x+(k*n)^2*f.val x)) = 0
  rw [fieldPair_helmholtz_integral _ Ω E hE i f, mul_pow]
  exact electric_lapPair k (n^2) hk (pow_ne_zero 2 hn) Ω E H hM i f

theorem electric_radial_equation (R L : ℝ) (hR : 0 ≤ R) (k n : ℂ)
    (hk : k ≠ 0) (hn : n ≠ 0) (E H : Field)
    (hM : TestMaxwell k (n^2) (AnnularMoment.annulus R L) E H)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (i : Fin 3) (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo R L) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * moment (fun x => E x i) (angularPolynomial p) r *
      radialExpression l (k*n) η r) = 0 := by
  apply WeakAnnularMoment.weak_radial_equation R L hR (k*n) _ (hE i)
  · exact electric_weak_helmholtz k n hk hn _ E H hM
      (locallyIntegrable_integrableTests _ E hE) i
  · exact hp
  · exact hh
  · exact hη
  · exact hc
  · exact hs

#print axioms OQ14.ComplexRegionalMaxwell.electric_weak_helmholtz
#print axioms OQ14.ComplexRegionalMaxwell.electric_radial_equation
end OQ14.ComplexRegionalMaxwell
