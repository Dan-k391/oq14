import OneDimensionalJump
import RadialMomentWeights

/-! Genuine radial continuity and flux jump from an actual weak point source. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialSourceJump

open MeasureTheory Filter Set OQ14.RadialMomentWeights OQ14.OneDimensionalJump
open scoped Topology

theorem coefficientA_smooth (l : ℕ) (U : ℝ → ℂ) (hU : ContDiffOn ℝ (⊤ : ℕ∞) U (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coefficientA l U) (Ioi 0) :=
  (Complex.ofRealCLM.contDiff.contDiffOn.pow (l+2)).mul hU

theorem coefficientAD_smooth (l : ℕ) (U : ℝ → ℂ) (hU : ContDiffOn ℝ (⊤ : ℕ∞) U (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coefficientAD l U (deriv U)) (Ioi 0) := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (deriv U) (Ioi 0) := hU.deriv_of_isOpen isOpen_Ioi (by simp)
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.contDiffOn.pow (l+1))).mul hU).add
    ((Complex.ofRealCLM.contDiff.contDiffOn.pow (l+2)).mul hD)

theorem coefficientB_smooth (l : ℕ) (U : ℝ → ℂ) (hU : ContDiffOn ℝ (⊤ : ℕ∞) U (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coefficientB l U) (Ioi 0) :=
  (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.contDiffOn.pow (l+1))).mul hU

theorem coefficient_source_residual (l : ℕ) (k : ℂ) (U : ℝ → ℂ) (r : ℝ)
    (hres : (r : ℂ)^2*deriv (deriv U) r+2*(r : ℂ)*deriv U r+
      (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*U r=0) :
    coefficientBD l U (deriv U) r-coefficientADD l U (deriv U) (deriv (deriv U)) r=coefficientC l k U r := by
  have h := coefficient_residual l k U (deriv U) (deriv (deriv U)) r
  rw [hres,mul_zero] at h
  linear_combination -h

theorem radial_point_source_jump (l : ℕ) (k : ℂ) (s : ℝ) (hs : 0 < s) (S : ℂ)
    (U Um Up : ℝ → ℂ)
    (hm : ContDiffOn ℝ (⊤ : ℕ∞) Um (Ioi 0)) (hp : ContDiffOn ℝ (⊤ : ℕ∞) Up (Ioi 0))
    (hOm : ∀ r : ℝ,r ∈ Ioi 0 →(r : ℂ)^2*deriv (deriv Um) r+2*(r : ℂ)*deriv Um r+
      (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*Um r=0)
    (hOp : ∀ r : ℝ,r ∈ Ioi 0 →(r : ℂ)^2*deriv (deriv Up) r+2*(r : ℂ)*deriv Up r+
      (k^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*Up r=0)
    (hUm : ∀ r ∈ Ioo 0 s,U r=Um r) (hUp : ∀ r,s < r → U r=Up r)
    (hweak : ∀ η : ℝ → ℂ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi (0 : ℝ) →
      (∫ r : ℝ,coefficientA l U r*deriv (deriv η) r+coefficientB l U r*deriv η r+
        coefficientC l k U r*η r)= -S*η s) :
    Up s=Um s ∧ (s : ℂ)^(l+2)*(deriv Up s-deriv Um s)= -S := by
  have hmD : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Um) (Ioi 0) := hm.deriv_of_isOpen isOpen_Ioi (by simp)
  have hpD : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Up) (Ioi 0) := hp.deriv_of_isOpen isOpen_Ioi (by simp)
  have hmd (r : ℝ) (hr : r ∈ Ioi 0) : HasDerivAt Um (deriv Um r) r :=
    ((hm.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hpd (r : ℝ) (hr : r ∈ Ioi 0) : HasDerivAt Up (deriv Up r) r :=
    ((hp.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hmdd (r : ℝ) (hr : r ∈ Ioi 0) : HasDerivAt (deriv Um) (deriv (deriv Um) r) r :=
    ((hmD.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hpdd (r : ℝ) (hr : r ∈ Ioi 0) : HasDerivAt (deriv Up) (deriv (deriv Up) r) r :=
    ((hpD.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hW : ∀ η : ℝ → ℂ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi (0 : ℝ) →
      (∫ r : ℝ,if r ≤ s then coefficientA l Um r*deriv (deriv η) r+coefficientB l Um r*deriv η r+
        (coefficientBD l Um (deriv Um) r-coefficientADD l Um (deriv Um) (deriv (deriv Um)) r)*η r
      else coefficientA l Up r*deriv (deriv η) r+coefficientB l Up r*deriv η r+
        (coefficientBD l Up (deriv Up) r-coefficientADD l Up (deriv Up) (deriv (deriv Up)) r)*η r)= -S*η s := by
    intro η hη hc hsub
    rw [← hweak η hη hc hsub]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ r : ℝ,r ≠ s from ae_iff.mpr (by simp)] with r hrs
    by_cases hr : 0 < r
    · by_cases hle : r ≤ s
      · have he := hUm r ⟨hr,lt_of_le_of_ne hle hrs⟩
        rw [if_pos hle,coefficient_source_residual l k Um r (hOm r hr)]
        simp only [coefficientA,coefficientB,coefficientC,he]
      · have he := hUp r (lt_of_not_ge hle)
        rw [if_neg hle,coefficient_source_residual l k Up r (hOp r hr)]
        simp only [coefficientA,coefficientB,coefficientC,he]
    · have hn : r ∉ tsupport η := fun h => hr (hsub h)
      have hv : η =ᶠ[𝓝 r] 0 := not_mem_tsupport_iff_eventuallyEq.mp hn
      have h1 : deriv η r=0 := by simpa only [deriv_zero] using hv.deriv_eq
      have h2 : deriv (deriv η) r=0 := by simpa only [deriv_zero] using hv.deriv.deriv_eq
      simp only [hv.eq_of_nhds,h1,h2,Pi.zero_apply,mul_zero,add_zero,ite_self]
  have hj := point_source_jump s hs S
    (coefficientA l Um) (coefficientAD l Um (deriv Um)) (coefficientADD l Um (deriv Um) (deriv (deriv Um)))
    (coefficientB l Um) (coefficientBD l Um (deriv Um))
    (coefficientA l Up) (coefficientAD l Up (deriv Up)) (coefficientADD l Up (deriv Up) (deriv (deriv Up)))
    (coefficientB l Up) (coefficientBD l Up (deriv Up))
    (coefficientA_smooth l Um hm) (coefficientAD_smooth l Um hm) (coefficientB_smooth l Um hm)
    (coefficientA_smooth l Up hp) (coefficientAD_smooth l Up hp) (coefficientB_smooth l Up hp)
    (fun r hr => coefficientA_hasDerivAt l Um (deriv Um) r (hmd r hr))
    (fun r hr => coefficientAD_hasDerivAt l Um (deriv Um) (deriv (deriv Um)) r (hmd r hr) (hmdd r hr))
    (fun r hr => coefficientB_hasDerivAt l Um (deriv Um) r (hmd r hr))
    (fun r hr => coefficientA_hasDerivAt l Up (deriv Up) r (hpd r hr))
    (fun r hr => coefficientAD_hasDerivAt l Up (deriv Up) (deriv (deriv Up)) r (hpd r hr) (hpdd r hr))
    (fun r hr => coefficientB_hasDerivAt l Up (deriv Up) r (hpd r hr)) hW
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hU : Up s=Um s := (mul_left_cancel₀ (pow_ne_zero (l+2) hsc)) hj.1
  refine ⟨hU,?_⟩
  have hb := hj.2
  simp only [coefficientB,coefficientAD] at hb
  rw [hU] at hb
  linear_combination -hb

end OQ14.RadialSourceJump

#print axioms OQ14.RadialSourceJump.coefficientA_smooth
#print axioms OQ14.RadialSourceJump.coefficientAD_smooth
#print axioms OQ14.RadialSourceJump.coefficientB_smooth
#print axioms OQ14.RadialSourceJump.coefficient_source_residual
#print axioms OQ14.RadialSourceJump.radial_point_source_jump
