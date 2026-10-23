import ScalarFiniteCalculus
import ScalarPlaneWaveMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual scalar angular integral jets and their finite-dimensional test functionals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.AngularScalarJets
open MeasureTheory Maxwell ModalDipole SphereReactionKernel SphereWaveCalculus
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem moment_second (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ) (hA : ∀ θ, ‖a θ‖ ≤ A)
    (k : ℝ) (x : Space) (i j : Fin 3) :
    dcoord (fun y => dcoord (moment a k) y i) x j=
      (Complex.I*(k : ℂ))^2*moment (fun θ => a θ*SphereWaveCalculus.coordinate i θ*SphereWaveCalculus.coordinate j θ) k x := by
  have hc : Continuous (fun θ => a θ*SphereWaveCalculus.coordinate i θ) := ha.mul (coordinate_continuous i)
  have hb (θ : Sphere) : ‖a θ*SphereWaveCalculus.coordinate i θ‖ ≤ A := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (coordinate_bound i θ) (norm_nonneg _)).trans (by simpa using hA θ)
  rw [show (fun y => dcoord (moment a k) y i)=
      (fun y => (Complex.I*(k : ℂ))*moment (fun θ => a θ*SphereWaveCalculus.coordinate i θ) k y) from
    funext (fun y => moment_partial a ha A hA k y i)]
  rw [partial_const_mul (moment_hasFDerivAt _ hc A hb k x).differentiableAt,moment_partial _ hc A hb k x j]
  simp only [SphereWaveCalculus.coordinate]
  ring

def planeJet (k : ℝ) (p : ι → Space) (θ : Sphere) : EdgeScalarInterpolation.Jet ι := fun q =>
  let w := SphereReactionKernel.wave k (p q.1) θ
  let d := Complex.I*(k : ℂ)
  match q.2.val with
  | 0 => w
  | 1 => d*SphereWaveCalculus.coordinate 0 θ*w
  | 2 => d*SphereWaveCalculus.coordinate 1 θ*w
  | 3 => d^2*SphereWaveCalculus.coordinate 0 θ*SphereWaveCalculus.coordinate 0 θ*w
  | 4 => d^2*SphereWaveCalculus.coordinate 1 θ*SphereWaveCalculus.coordinate 0 θ*w
  | _ => d^2*SphereWaveCalculus.coordinate 1 θ*SphereWaveCalculus.coordinate 1 θ*w

omit [Fintype ι] in
theorem planeJet_continuous (k : ℝ) (p : ι → Space) : Continuous (planeJet k p) := by
  apply continuous_pi
  rintro ⟨j,n⟩
  have hw : Continuous (SphereReactionKernel.wave k (p j)) := by unfold SphereReactionKernel.wave; fun_prop
  have h0 := coordinate_continuous 0
  have h1 := coordinate_continuous 1
  fin_cases n <;> dsimp only [planeJet]
  · exact hw
  all_goals fun_prop (disch := assumption)

omit [Fintype ι] in
theorem jet_moment (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ) (hA : ∀ θ, ‖a θ‖ ≤ A)
    (k : ℝ) (p : ι → Space) :
    SymmetricScalarJets.jet (moment a k) p=fun q => ∫ θ : Sphere, a θ*planeJet k p θ q ∂surface := by
  funext q
  rcases q with ⟨j,n⟩
  fin_cases n <;> dsimp only [SymmetricScalarJets.jet,planeJet]
  · rfl
  all_goals try rw [moment_second a ha A hA]
  all_goals try rw [moment_partial a ha A hA]
  all_goals unfold moment
  all_goals rw [← integral_const_mul]
  all_goals apply integral_congr_ae
  all_goals filter_upwards with θ
  all_goals simp only [SphereWaveCalculus.coordinate]
  all_goals ring

theorem functional_moment (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ) (hA : ∀ θ, ‖a θ‖ ≤ A)
    (k : ℝ) (p : ι → Space) (L : EdgeScalarInterpolation.Jet ι →ₗ[ℂ] ℂ) :
    L (SymmetricScalarJets.jet (moment a k) p)=
      ∫ θ : Sphere, a θ*L (planeJet k p θ) ∂surface := by
  have hi : Integrable (fun θ : Sphere => a θ • planeJet k p θ) surface :=
    (ha.smul (planeJet_continuous k p)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : SymmetricScalarJets.jet (moment a k) p=∫ θ : Sphere, a θ • planeJet k p θ ∂surface := by
    rw [jet_moment a ha A hA k p]
    funext q
    simpa only [ContinuousLinearMap.proj_apply,Pi.smul_apply,smul_eq_mul] using
      (ContinuousLinearMap.proj q : EdgeScalarInterpolation.Jet ι →L[ℂ] ℂ).integral_comp_comm hi
  rw [he]
  have hL := L.toContinuousLinearMap.integral_comp_comm hi
  simpa only [LinearMap.coe_toContinuousLinearMap',map_smul,smul_eq_mul] using hL.symm

end OQ14.AngularScalarJets
#print axioms OQ14.AngularScalarJets.moment_second
#print axioms OQ14.AngularScalarJets.planeJet_continuous
#print axioms OQ14.AngularScalarJets.jet_moment
#print axioms OQ14.AngularScalarJets.functional_moment
