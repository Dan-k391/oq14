import FiniteMixedTraces
import SphereVectorPairing

/-! Limit of the actual sphere pairing of the finite incoming electric and magnetic trace maps. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.FiniteMixedFlux
open Complex Filter MeasureTheory OQ14.Maxwell OQ14.SphereVectorPairing
open OQ14.SphereReactionKernel OQ14.FiniteMixedTraces OQ14.ComplexTransverseExpansion
open scoped Topology

theorem pairing_smul_smul (a b : ℂ) (F G : C(Sphere,Vector)) :
    pairing (a • F) (b • G)=a*(starRingEnd ℂ) b*pairing F G := by
  have h := integral_smul (μ := surface) (a*(starRingEnd ℂ) b) (fun n : Sphere => dot (F n) (conjugate (G n)))
  simp only [smul_eq_mul] at h
  rw [pairing_integral,pairing_integral,←h]
  apply integral_congr_ae
  filter_upwards with n
  simp only [ContinuousMap.smul_apply,dot,conjugate,Pi.smul_apply,smul_eq_mul,map_mul]
  ring

theorem pairing_limit (c : ModeIndex →₀ ℂ) :
    Tendsto (fun r : ℝ => pairing (electricMap c r) (magneticMap c r)) atTop
      (𝓝 (((2*Real.pi : ℂ)*I)*(starRingEnd ℂ) ((2*Real.pi : ℂ)*I)*pairing (amplitude c) (amplitude c))) := by
  have h := (pairing_continuous.tendsto ((((2*Real.pi : ℂ)*I) • amplitude c,((2*Real.pi : ℂ)*I) • amplitude c))).comp
    ((electricMap_limit c).prodMk_nhds (magneticMap_limit c))
  simpa only [Function.comp_def,pairing_smul_smul] using h

theorem pairing_limit_real (c : ModeIndex →₀ ℂ) :
    Tendsto (fun r : ℝ => pairing (electricMap c r) (magneticMap c r)) atTop
      (𝓝 (((4*Real.pi^2 : ℝ) : ℂ)*pairing (amplitude c) (amplitude c))) := by
  have he : ((2*Real.pi : ℂ)*I)*(starRingEnd ℂ) ((2*Real.pi : ℂ)*I)=((4*Real.pi^2 : ℝ) : ℂ) := by
    simp only [map_mul,map_ofNat,conj_ofReal,conj_I,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
    have : I*(-I)=(1 : ℂ) := by norm_num
    calc
      _ = (2*(Real.pi : ℂ))*(2*(Real.pi : ℂ))*(I*(-I)) := by ring
      _ = _ := by rw [this]; ring
  simpa only [he] using pairing_limit c

end OQ14.FiniteMixedFlux
#print axioms OQ14.FiniteMixedFlux.pairing_smul_smul
#print axioms OQ14.FiniteMixedFlux.pairing_limit
#print axioms OQ14.FiniteMixedFlux.pairing_limit_real
