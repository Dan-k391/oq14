import HarmonicMomentSeparation
import SphereReactionKernel

/-! Genuine angular energy pairings of finite continuous amplitude sums. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.AngularFinitePairing
open MeasureTheory Maxwell SphereReactionKernel
variable {κ : Type*}

def integralMap : C(Sphere,ℂ) →L[ℝ] ℂ :=
  (L1.integralCLM (α := Sphere) (E := ℂ) (μ := surface)).comp
    (ContinuousMap.toLp 1 surface ℝ)

theorem integralMap_apply (f : C(Sphere,ℂ)) : integralMap f=∫ n, f n ∂surface := by
  change L1.integralCLM (ContinuousMap.toLp 1 surface ℝ f)=_
  rw [← L1.integral_eq,L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) surface f

def combo (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (u : κ → ℂ) (j : Fin 3) : C(Sphere,ℂ) :=
  ∑ i ∈ s, u i • T i j

theorem combo_continuous (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (j : Fin 3) :
    Continuous (fun u : κ → ℂ => combo s T u j) := by
  apply continuous_finset_sum
  intro i _
  exact (continuous_apply i).smul continuous_const

def conjugateMap : C(Sphere,ℂ) →L[ℝ] C(Sphere,ℂ) :=
  Complex.conjCLE.toContinuousLinearMap.compLeftContinuousCompact Sphere

def pairing (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (u v : κ → ℂ) : ℂ :=
  integralMap (∑ j : Fin 3, combo s T u j*conjugateMap (combo s T v j))

theorem pairing_continuous (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) :
    Continuous (fun uv : (κ → ℂ) × (κ → ℂ) => pairing s T uv.1 uv.2) := by
  apply integralMap.continuous.comp
  apply continuous_finset_sum
  intro j _
  exact ((combo_continuous s T j).comp continuous_fst).mul
    (conjugateMap.continuous.comp ((combo_continuous s T j).comp continuous_snd))

theorem pairing_integral (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (u v : κ → ℂ) :
    pairing s T u v=∫ n : Sphere, dot (fun j => ∑ i ∈ s, u i*T i j n)
      (conjugate (fun j => ∑ i ∈ s, v i*T i j n)) ∂surface := by
  rw [pairing,integralMap_apply]
  apply integral_congr_ae
  filter_upwards with n
  simp [combo,conjugateMap,Complex.conjCLE_apply,dot,conjugate,Fin.sum_univ_three]

theorem energy_integrable (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (u : κ → ℂ) :
    Integrable (fun n : Sphere => energy (fun j => ∑ i ∈ s, u i*T i j n)) surface := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  unfold energy
  fun_prop

theorem pairing_self (s : Finset κ) (T : κ → Fin 3 → C(Sphere,ℂ)) (u : κ → ℂ) :
    (pairing s T u u).re=∫ n : Sphere, energy (fun j => ∑ i ∈ s, u i*T i j n) ∂surface := by
  rw [pairing_integral]
  simp_rw [Maxwell.dot_conjugate]
  exact congrArg Complex.re (integral_ofReal (𝕜 := ℂ) (μ := surface)
    (f := fun n : Sphere => energy (fun j => ∑ i ∈ s, u i*T i j n)))

end OQ14.AngularFinitePairing
#print axioms OQ14.AngularFinitePairing.integralMap_apply
#print axioms OQ14.AngularFinitePairing.combo_continuous
#print axioms OQ14.AngularFinitePairing.pairing_continuous
#print axioms OQ14.AngularFinitePairing.pairing_integral
#print axioms OQ14.AngularFinitePairing.energy_integrable
#print axioms OQ14.AngularFinitePairing.pairing_self
