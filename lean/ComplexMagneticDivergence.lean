import ComplexMagneticHelmholtz

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexMagneticDivergence
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.RegionalMaxwellHelmholtz
  OQ14.ComplexSphereMaxwell
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem magnetic_divergence (k ε : ℂ) (hk : k ≠ 0) (Ω : Set Space) (E H : Field)
    (hM : ComplexRegionalMaxwell.TestMaxwell k ε Ω E H) (f : Test Ω) :
    divPair (fieldPair H) f = 0 :=
  divPair_zero_of_curl (fieldPair E) (fieldPair H) (I*k) (mul_ne_zero I_ne_zero hk)
    (fun i g => (hM i g).1) f

theorem interior (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (f : Test (ball 0 1)) : divPair (fieldPair (magnetic n hn z u)) f = 0 :=
  magnetic_divergence z ((n : ℂ)^2) hz _ _ _ (interior_maxwell n hn z T hT u hker) f

theorem exterior (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 0 ≤ T+1)
    (u : VectorL2) (f : Test ((ball 0 T) \ (closedBall 0 1))) :
    divPair (fieldPair (magnetic n hn z u)) f = 0 :=
  magnetic_divergence z 1 hz _ _ _ (exterior_maxwell n hn z T hT u) f

#print axioms OQ14.ComplexMagneticDivergence.interior
#print axioms OQ14.ComplexMagneticDivergence.exterior
#print axioms OQ14.ComplexMagneticDivergence.magnetic_divergence
end OQ14.ComplexMagneticDivergence
