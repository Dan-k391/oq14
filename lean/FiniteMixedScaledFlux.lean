import FiniteMixedInwardFlux
import FiniteMixedHerglotz

/-! Frequency-k inward power of the finite incoming half-fields and unit-limit normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.FiniteMixedScaledFlux
open Complex Filter MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.FiniteMixedTraces
open OQ14.ComplexTransverseExpansion OQ14.FiniteMixedFields OQ14.FiniteMixedInwardFlux
open scoped Topology

def electricPartK (k : ℝ) (c : ModeIndex →₀ ℂ) : Field := fun x => electricPart c true (k • x)
def magneticPartK (k : ℝ) (c : ModeIndex →₀ ℂ) : Field := fun x => magneticPart c true (k • x)

def inwardPowerK (k : ℝ) (c : ModeIndex →₀ ℂ) (r : ℝ) : ℝ :=
  -r^2*∫ n : Sphere,FarFieldPower.radialPower (n : Space) (electricPartK k c (r • (n : Space)))
    (magneticPartK k c (r • (n : Space))) ∂SphereReactionKernel.surface

theorem inwardPowerK_eq (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) (r : ℝ) :
    inwardPowerK k c r=inwardPower c (k*r)/k^2 := by
  have hI : (∫ n : Sphere,FarFieldPower.radialPower (n : Space) (electricPartK k c (r • (n : Space)))
      (magneticPartK k c (r • (n : Space))) ∂SphereReactionKernel.surface)=
      ∫ n : Sphere,FarFieldPower.radialPower (n : Space) (electricPart c true ((k*r) • (n : Space)))
        (magneticPart c true ((k*r) • (n : Space))) ∂SphereReactionKernel.surface := by
    simp only [electricPartK,magneticPartK,smul_smul]
  unfold inwardPowerK inwardPower
  rw [hI]
  have hk2 : k^2≠0 := by positivity
  field_simp
  ring

def energyIntegral (c : ModeIndex →₀ ℂ) : ℝ :=
  ∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface

def E (c : ModeIndex →₀ ℂ) : ℝ := 2*Real.pi^2*energyIntegral c

theorem inwardPowerK_limit (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) :
    Tendsto (inwardPowerK k c) atTop
      (𝓝 ((2*Real.pi^2/k^2)*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface)) := by
  have h := ((inwardPower_limit c).comp (tendsto_id.const_mul_atTop hk)).div_const (k^2)
  have he : (2*Real.pi^2*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface)/k^2=
      (2*Real.pi^2/k^2)*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface := by ring
  rw [he] at h
  refine h.congr ?_
  intro r
  exact (inwardPowerK_eq k hk c r).symm

theorem inwardPowerK_limit_E (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) :
    Tendsto (inwardPowerK k c) atTop (𝓝 (E c/k^2)) := by
  have h := inwardPowerK_limit k hk c
  have he : (2*Real.pi^2/k^2)*∫ n : Sphere,Maxwell.energy (amplitude c n) ∂SphereReactionKernel.surface=E c/k^2 := by
    unfold E energyIntegral
    ring
  rwa [he] at h

theorem amplitude_smul (z : ℂ) (c : ModeIndex →₀ ℂ) : amplitude (z • c)=z • amplitude c := by
  apply ContinuousMap.ext
  intro n
  funext i
  rw [amplitude_apply]
  simp only [ContinuousMap.smul_apply,Pi.smul_apply,smul_eq_mul,amplitude_apply,Finsupp.smul_apply,Finset.mul_sum]
  rw [Finset.sum_subset Finsupp.support_smul]
  · apply Finset.sum_congr rfl
    intro m _
    ring
  · intro m _ hm
    have h0 : (z • c) m=0 := Finsupp.not_mem_support_iff.mp hm
    simp only [Finsupp.smul_apply,smul_eq_mul] at h0
    rw [h0]
    ring

theorem energy_smul_vector (z : ℂ) (v : Vector) : Maxwell.energy (z • v)=Complex.normSq z*Maxwell.energy v := by
  simp only [Maxwell.energy,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul]
  ring

theorem energyIntegral_smul (t : ℝ) (c : ModeIndex →₀ ℂ) :
    energyIntegral ((t : ℂ) • c)=t^2*energyIntegral c := by
  unfold energyIntegral
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with n
  rw [amplitude_smul]
  change Maxwell.energy ((t : ℂ) • amplitude c n)=_
  rw [energy_smul_vector,Complex.normSq_ofReal]
  ring

theorem E_smul (t : ℝ) (c : ModeIndex →₀ ℂ) : E ((t : ℂ) • c)=t^2*E c := by
  unfold E
  rw [energyIntegral_smul]
  ring

theorem E_pos (c : ModeIndex →₀ ℂ) (hc : c≠0) : 0<E c :=
  inwardPower_limit_pos c hc

def normalize (c : ModeIndex →₀ ℂ) : ModeIndex →₀ ℂ := (((Real.sqrt (E c))⁻¹ : ℝ) : ℂ) • c

theorem normalize_ne_zero (c : ModeIndex →₀ ℂ) (hc : c≠0) : normalize c≠0 := by
  have hs : (((Real.sqrt (E c))⁻¹ : ℝ) : ℂ)≠0 := by
    have := Real.sqrt_pos.mpr (E_pos c hc)
    exact_mod_cast inv_ne_zero this.ne'
  exact smul_ne_zero hs hc

theorem E_normalize (c : ModeIndex →₀ ℂ) (hc : c≠0) : E (normalize c)=1 := by
  unfold normalize
  rw [E_smul,inv_pow,Real.sq_sqrt (E_pos c hc).le]
  exact inv_mul_cancel₀ (E_pos c hc).ne'

theorem normalized_limit (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    Tendsto (inwardPower (normalize c)) atTop (𝓝 1) := by
  have h := inwardPower_limit (normalize c)
  have he : 2*Real.pi^2*∫ n : Sphere,Maxwell.energy (amplitude (normalize c) n) ∂SphereReactionKernel.surface=1 := by
    have := E_normalize c hc
    unfold E energyIntegral at this
    exact this
  rwa [he] at h

theorem normalized_limit_K (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    Tendsto (inwardPowerK k (normalize c)) atTop (𝓝 (1/k^2)) := by
  have h := inwardPowerK_limit_E k hk (normalize c)
  rwa [E_normalize c hc] at h

def normalizeK (k : ℝ) (c : ModeIndex →₀ ℂ) : ModeIndex →₀ ℂ := (k : ℂ) • normalize c

theorem normalizeK_ne_zero (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) (hc : c≠0) : normalizeK k c≠0 :=
  smul_ne_zero (by exact_mod_cast hk.ne') (normalize_ne_zero c hc)

theorem normalizedK_limit (k : ℝ) (hk : 0<k) (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    Tendsto (inwardPowerK k (normalizeK k c)) atTop (𝓝 1) := by
  have h := inwardPowerK_limit_E k hk (normalizeK k c)
  have he : E (normalizeK k c)/k^2=1 := by
    unfold normalizeK
    rw [E_smul,E_normalize c hc]
    field_simp
  rwa [he] at h

end OQ14.FiniteMixedScaledFlux
#print axioms OQ14.FiniteMixedScaledFlux.inwardPowerK_eq
#print axioms OQ14.FiniteMixedScaledFlux.inwardPowerK_limit
#print axioms OQ14.FiniteMixedScaledFlux.inwardPowerK_limit_E
#print axioms OQ14.FiniteMixedScaledFlux.amplitude_smul
#print axioms OQ14.FiniteMixedScaledFlux.energy_smul_vector
#print axioms OQ14.FiniteMixedScaledFlux.energyIntegral_smul
#print axioms OQ14.FiniteMixedScaledFlux.E_smul
#print axioms OQ14.FiniteMixedScaledFlux.E_pos
#print axioms OQ14.FiniteMixedScaledFlux.normalize_ne_zero
#print axioms OQ14.FiniteMixedScaledFlux.E_normalize
#print axioms OQ14.FiniteMixedScaledFlux.normalized_limit
#print axioms OQ14.FiniteMixedScaledFlux.normalized_limit_K
#print axioms OQ14.FiniteMixedScaledFlux.normalizeK_ne_zero
#print axioms OQ14.FiniteMixedScaledFlux.normalizedK_limit
