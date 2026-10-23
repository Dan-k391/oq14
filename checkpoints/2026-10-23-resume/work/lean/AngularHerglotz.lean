import SphereMomentSmooth
import ConicalPlaneWaves

/-! Actual entire Maxwell fields of continuous transverse angular amplitudes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.AngularHerglotz
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel OQ14.SphereWaveCalculus
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere

def electric (k : ℝ) (A : Sphere → Vector) : Field := fun x i => moment (fun θ => A θ i) (-k) x

def magneticAmplitude (A : Sphere → Vector) (θ : Sphere) : Vector :=
  -crossProduct (ConicalPlaneWaves.direction θ) (A θ)

def magnetic (k : ℝ) (A : Sphere → Vector) : Field := electric k (magneticAmplitude A)

theorem magneticAmplitude_continuous (A : Sphere → Vector) (hA : ∀ i, Continuous (fun θ => A θ i)) (i : Fin 3) :
    Continuous (fun θ => magneticAmplitude A θ i) := by
  fin_cases i <;> simp only [magneticAmplitude,Pi.neg_apply,cross_apply,ConicalPlaneWaves.direction]
  all_goals exact ((coordinate_continuous _).mul (hA _)).sub ((coordinate_continuous _).mul (hA _)) |>.neg

theorem electric_smooth (k : ℝ) (A : Sphere → Vector) (hA : ∀ i, Continuous (fun θ => A θ i)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric k A x i) := SphereMomentSmooth.moment_smooth _ (hA i) (-k)

theorem magnetic_smooth (k : ℝ) (A : Sphere → Vector) (hA : ∀ i, Continuous (fun θ => A θ i)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic k A x i) :=
  electric_smooth k _ (magneticAmplitude_continuous A hA) i

theorem curl_electric (k : ℝ) (A : Sphere → Vector) (hA : ∀ i, Continuous (fun θ => A θ i))
    (x : Space) (i : Fin 3) :
    curl (electric k A) x i=Complex.I*(k : ℂ)*magnetic k A x i := by
  have hp (j l : Fin 3) : dcoord (fun y => electric k A y j) x l=
      -(Complex.I*(k : ℂ))*moment (fun θ => A θ j*SphereWaveCalculus.coordinate l θ) (-k) x := by
    obtain ⟨B,hB⟩ := SphereMomentSmooth.amplitude_bound_exists _ (hA j)
    simpa only [Complex.ofReal_neg,mul_neg,neg_mul] using moment_partial _ (hA j) B hB (-k) x l
  have hi (j l : Fin 3) : Integrable (fun θ => A θ j*SphereWaveCalculus.coordinate l θ*wave (-k) x θ) surface :=
    (((hA j).mul (coordinate_continuous l)).mul (by unfold wave; fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : curl (electric k A) x i=dcoord (fun y => electric k A y (WeakCurl.previous i)) x (WeakCurl.next i)-
      dcoord (fun y => electric k A y (WeakCurl.next i)) x (WeakCurl.previous i) := by fin_cases i <;> rfl
  rw [hc,hp,hp]
  have hmag : magnetic k A x i= -
      (moment (fun θ => A θ (WeakCurl.previous i)*SphereWaveCalculus.coordinate (WeakCurl.next i) θ) (-k) x-
       moment (fun θ => A θ (WeakCurl.next i)*SphereWaveCalculus.coordinate (WeakCurl.previous i) θ) (-k) x) := by
    simp only [magnetic,electric,moment]
    rw [← integral_sub (hi _ _) (hi _ _),← integral_neg]
    apply integral_congr_ae
    filter_upwards with θ
    fin_cases i <;> simp [magneticAmplitude,cross_apply,ConicalPlaneWaves.direction,SphereWaveCalculus.coordinate,WeakCurl.next,WeakCurl.previous] <;> ring
  rw [hmag]
  ring

theorem magneticAmplitude_twice (A : Sphere → Vector) (hA : ∀ θ : Sphere, dot (ConicalPlaneWaves.direction θ) (A θ)=0)
    (θ : Sphere) : magneticAmplitude (magneticAmplitude A) θ= -A θ := by
  have hs := ConicalPlaneWaves.direction_norm_sq (θ : Space) (AngularPower.sphere_norm θ)
  have ht := hA θ
  simp only [dot,ConicalPlaneWaves.direction] at ht
  ext i
  fin_cases i <;> simp [magneticAmplitude,cross_apply,ConicalPlaneWaves.direction]
  · linear_combination -(A θ 0)*hs+(θ.val 0 : ℂ)*ht
  · linear_combination -(A θ 1)*hs+(θ.val 1 : ℂ)*ht
  · linear_combination -(A θ 2)*hs+(θ.val 2 : ℂ)*ht

theorem maxwell_at (k : ℝ) (A : Sphere → Vector) (hA : ∀ i, Continuous (fun θ => A θ i))
    (ht : ∀ θ : Sphere, dot (ConicalPlaneWaves.direction θ) (A θ)=0) (x : Space) :
    MaxwellAt k 1 1 (electric k A) (magnetic k A) x := by
  constructor
  · ext i
    simpa only [Complex.ofReal_one,mul_one] using curl_electric k A hA x i
  · ext i
    have h := curl_electric k (magneticAmplitude A) (magneticAmplitude_continuous A hA) x i
    have he : magnetic k (magneticAmplitude A) x i= -electric k A x i := by
      simp only [magnetic,electric,magneticAmplitude_twice A ht,Pi.neg_apply,moment,neg_mul,integral_neg]
    rw [he] at h
    simpa only [Complex.ofReal_one,mul_one,mul_neg,neg_mul] using h

end OQ14.AngularHerglotz
#print axioms OQ14.AngularHerglotz.magneticAmplitude_continuous
#print axioms OQ14.AngularHerglotz.electric_smooth
#print axioms OQ14.AngularHerglotz.magnetic_smooth
#print axioms OQ14.AngularHerglotz.curl_electric
#print axioms OQ14.AngularHerglotz.magneticAmplitude_twice
#print axioms OQ14.AngularHerglotz.maxwell_at
