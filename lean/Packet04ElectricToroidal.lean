import Packet04VectorTests
import Packet04RadialCurl
import Packet02MagneticVanishing
import Packet01MomentIntegrability

/-! Vanishing of actual electric toroidal moments from global magnetic radial
vanishing and the weak first Maxwell equation. No interface trace is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04ElectricToroidal
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.RegionalMaxwellHelmholtz OQ14.DebyeCalculus OQ14.Packet04VectorTests
  OQ14.WeakDebyeScalar OQ14.ComplexSphereMaxwell OQ14.ModalWeightedMode
  OQ14.AngularPower OQ14.HarmonicPolynomial
open OQ14.ModalMeridionalReflection

def radialTest (Ω : Set Space) (φ : Space → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) (j : Fin 3) : Test Ω :=
  ⟨fun x => (x j : ℂ)*φ x, (coordinate j).contDiff.mul hφ,
    hc.mul_left, tsupport_mul_subset_right.trans hs⟩

theorem radial_test_annihilation (Ω : Set Space) (E H : Field) (a : ℂ)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hcurl : ∀ (i : Fin 3) (f : Test Ω), curlPair (fieldPair E) i f = a * fieldPair H i f)
    (hzero : ∀ᵐ x ∂volume, radialDot (fun j y => H y j) x = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∫ x, ∑ j : Fin 3, E x j * toroidal φ x j) = 0 := by
  have h := weak_vector_curl Ω E H a hE hH hcurl (radialTest Ω φ hφ hc hs)
  have hz : (∫ x, ∑ j : Fin 3, H x j * (radialTest Ω φ hφ hc hs j).val x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with x hx
    change (∑ j : Fin 3, H x j * ((x j : ℂ) * φ x)) = 0
    calc
      _ = (∑ j : Fin 3, (x j : ℂ) * H x j) * φ x := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
      _ = 0 := by change radialDot (fun j y => H y j) x * φ x = 0; rw [hx, zero_mul]
  rw [hz, mul_zero] at h
  exact h

theorem actual_test_annihilation (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball (0 : Space) T) :
    (∫ x, ∑ j : Fin 3, electric n hn z T u x j * toroidal φ x j) = 0 :=
  radial_test_annihilation _ _ _ (I*z)
    (Packet04WeakSphereMaxwell.electric_local n hn z T u)
    (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (fun i f => (Packet04WeakSphereMaxwell.actual_maxwell n hn z T hT u hker i f).1)
    (Packet02MagneticVanishing.radial_zero_ae n hn u hu z) φ hφ hc hs

end OQ14.Packet04ElectricToroidal
#print axioms OQ14.Packet04ElectricToroidal.radial_test_annihilation
#print axioms OQ14.Packet04ElectricToroidal.actual_test_annihilation
