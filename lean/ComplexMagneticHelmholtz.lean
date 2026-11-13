import ComplexSphereMaxwell
import ComplexExteriorHelmholtz

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexMagneticHelmholtz
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.RegionalMaxwellHelmholtz
  OQ14.WeakHelmholtzRegularity OQ14.ExteriorHelmholtz OQ14.ComplexSphereMaxwell
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem magnetic_lapPair (k ε : ℂ) (hk : k ≠ 0) (Ω : Set Space) (E H : Field)
    (hM : ComplexRegionalMaxwell.TestMaxwell k ε Ω E H) (i : Fin 3) (f : Test Ω) :
    lapPair (fieldPair H) i f+(k^2*ε)*fieldPair H i f = 0 := by
  have hb : I*k ≠ 0 := mul_ne_zero I_ne_zero hk
  have h := pair_helmholtz (fieldPair H) (fieldPair E) (-(I*k*ε)) (I*k) hb
    (fun j g => (hM j g).2) (fun j g => (hM j g).1) i f
  convert h using 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

theorem magnetic_weak_helmholtz (k n : ℂ) (hk : k ≠ 0) (Ω : Set Space) (E H : Field)
    (hM : ComplexRegionalMaxwell.TestMaxwell k (n^2) Ω E H) (hH : IntegrableTests Ω H)
    (i : Fin 3) : IsWeakHelmholtz (k*n) Ω (fun x => H x i) := by
  intro φ hφ hc hs
  let f : Test Ω := ⟨φ,hφ,hc,hs⟩
  change (∫ x, H x i*(laplacian f.val x+(k*n)^2*f.val x)) = 0
  rw [fieldPair_helmholtz_integral _ Ω H hH i f, mul_pow]
  exact magnetic_lapPair k (n^2) hk Ω E H hM i f

theorem magnetic_local (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (i : Fin 3) :
    LocallyIntegrable (fun x => magnetic n hn z u x i) :=
  ComplexMagneticLocal.magnetic_locallyIntegrable z 1 (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) u)
    (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u)
    (DynamicVolume.source_integrable _ u 1 (ModalWeightedMode.coefficient_support n hn))
    (DynamicVolume.source_zero _ u 1 (ModalWeightedMode.coefficient_support n hn))
    (StaticNewton.material_source_ae _ u) i

theorem interior (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) : IsWeakHelmholtz (z*n) (ball 0 1) (fun x => magnetic n hn z u x i) :=
  magnetic_weak_helmholtz z n hz _ _ _ (interior_maxwell n hn z T hT u hker)
    (locallyIntegrable_integrableTests _ _ (magnetic_local n hn z u)) i

theorem exterior (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 0 ≤ T+1)
    (u : VectorL2) (i : Fin 3) : IsWeakHelmholtz z ((ball 0 T) \ (closedBall 0 1))
      (fun x => magnetic n hn z u x i) := by
  simpa only [mul_one, one_pow] using
    magnetic_weak_helmholtz z 1 hz _ _ _ (by simpa using exterior_maxwell n hn z T hT u)
      (locallyIntegrable_integrableTests _ _ (magnetic_local n hn z u)) i

#print axioms OQ14.ComplexMagneticHelmholtz.interior
#print axioms OQ14.ComplexMagneticHelmholtz.exterior
#print axioms OQ14.ComplexMagneticHelmholtz.magnetic_lapPair
#print axioms OQ14.ComplexMagneticHelmholtz.magnetic_weak_helmholtz
#print axioms OQ14.ComplexMagneticHelmholtz.magnetic_local
end OQ14.ComplexMagneticHelmholtz
