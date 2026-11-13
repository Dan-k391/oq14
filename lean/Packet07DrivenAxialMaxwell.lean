import Packet07DrivenAxialCurl
import Packet06ComplexAffine

/-! Genuine weak Maxwell covariance under arbitrary axial rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialMaxwell
open MeasureTheory Maxwell DynamicSource MaterialMaxwell MagneticResponse ModalAxialRotation
  Packet06ComplexAffine Packet07DrivenAxialTests Packet07DrivenAxialPair Packet07DrivenAxialCurl

theorem dielectric_rotate (θ : ℝ) (ε : Space → ℝ) (E : Field) (x : Space) (i : Fin 3) :
    ((ε (rotation (-θ) x) : ℝ) : ℂ)*rotateField θ E x i =
      rotateField θ (fun y j => (ε y : ℂ)*E y j) x i := by
  fin_cases i <;> simp [rotateField,vector] <;> ring

theorem complex_maxwell_rotate (θ : ℝ) (z : ℂ) (ε : Space → ℝ) (E H : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hεE : ∀ i, LocallyIntegrable (fun x => (ε x : ℂ)*E x i)) (hM : TestMaxwellC z ε E H) :
    TestMaxwellC z (fun x => ε (rotation (-θ) x)) (rotateField θ E) (rotateField θ H) := by
  let G : Field := fun x i => (ε x : ℂ)*E x i
  have hg : ∀ i f, (∫ x, ((ε (rotation (-θ) x) : ℝ) : ℂ)*rotateField θ E x i*f.val x) =
      fieldPair (rotateField θ G) i f := by
    intro i f
    apply integral_congr_ae
    filter_upwards with x
    rw [dielectric_rotate]
  intro i f
  have h0 := hM 0 (rotateTest θ f)
  have h1 := hM 1 (rotateTest θ f)
  have h2 := hM 2 (rotateTest θ f)
  change curlPair (fieldPair E) 0 (rotateTest θ f) = Complex.I*z*fieldPair H 0 (rotateTest θ f) ∧
    curlPair (fieldPair H) 0 (rotateTest θ f) = -(Complex.I*z)*fieldPair G 0 (rotateTest θ f) at h0
  change curlPair (fieldPair E) 1 (rotateTest θ f) = Complex.I*z*fieldPair H 1 (rotateTest θ f) ∧
    curlPair (fieldPair H) 1 (rotateTest θ f) = -(Complex.I*z)*fieldPair G 1 (rotateTest θ f) at h1
  change curlPair (fieldPair E) 2 (rotateTest θ f) = Complex.I*z*fieldPair H 2 (rotateTest θ f) ∧
    curlPair (fieldPair H) 2 (rotateTest θ f) = -(Complex.I*z)*fieldPair G 2 (rotateTest θ f) at h2
  rw [hg]
  fin_cases i <;> simp only
  · change curlPair (fieldPair (rotateField θ E)) 0 f = Complex.I*z*fieldPair (rotateField θ H) 0 f ∧
      curlPair (fieldPair (rotateField θ H)) 0 f = -(Complex.I*z)*fieldPair (rotateField θ G) 0 f
    rw [curl_pair_zero θ E hE,curl_pair_zero θ H hH,field_pair_zero θ H hH,field_pair_zero θ G hεE]
    constructor <;> simp only [h0.1,h1.1,h0.2,h1.2] <;> ring
  · change curlPair (fieldPair (rotateField θ E)) 1 f = Complex.I*z*fieldPair (rotateField θ H) 1 f ∧
      curlPair (fieldPair (rotateField θ H)) 1 f = -(Complex.I*z)*fieldPair (rotateField θ G) 1 f
    rw [curl_pair_one θ E hE,curl_pair_one θ H hH,field_pair_one θ H hH,field_pair_one θ G hεE]
    constructor <;> simp only [h0.1,h1.1,h0.2,h1.2] <;> ring
  · change curlPair (fieldPair (rotateField θ E)) 2 f = Complex.I*z*fieldPair (rotateField θ H) 2 f ∧
      curlPair (fieldPair (rotateField θ H)) 2 f = -(Complex.I*z)*fieldPair (rotateField θ G) 2 f
    rw [curl_pair_two θ E hE,curl_pair_two θ H hH,field_pair_two θ H,field_pair_two θ G]
    exact h2
end OQ14.Packet07DrivenAxialMaxwell
#print axioms OQ14.Packet07DrivenAxialMaxwell.dielectric_rotate
#print axioms OQ14.Packet07DrivenAxialMaxwell.complex_maxwell_rotate
