import DensityCurl
import RadialInterface
import MaxwellRadiation
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Genuine weak curl pairings of actual density fields from derived partial bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DensityWeak
open MeasureTheory Metric Set Maxwell DensityCurl MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space

theorem coordinate_bound (K : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (x : Space) (a i : Fin 3) :
    ‖dcoord (fun z => field K ρ z i) x a‖ ≤ D*sourceMass ρ := by
  rw [coordinate_derivative K ρ hρ hd hc D hb hi]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ∫ y, ‖ρ j y*dcoord (fun z => K z y i j) x a‖ :=
      Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm _)
    _ ≤ ∑ j : Fin 3, D*(∫ y, ‖ρ j y‖) := Finset.sum_le_sum (fun j _ => by
      rw [← integral_const_mul]
      apply integral_mono_ae
        (DensityDerivatives.partial_integrable (fun x y => K x y i j) (ρ j) (hρ j) x (hc x i j) D
          (fun y => hb x y i j) a).norm ((hρ j).norm.const_mul D)
      filter_upwards with y
      have hpoint : ‖dcoord (fun z => K z y i j) x a‖ ≤ D := by
        unfold dcoord
        have hp := (fderiv ℝ (fun z => K z y i j) x).le_opNorm (basis a)
        have hnorm : ‖basis a‖=1 := by simp [basis]
        rw [hnorm,mul_one] at hp
        exact hp.trans (hb x y i j)
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)).trans_eq (by ring))
    _ = _ := by unfold sourceMass; rw [Finset.mul_sum]

theorem partial_locallyIntegrable (K : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (a i : Fin 3) :
    LocallyIntegrable (fun x => pd (field K ρ) x a i) := by
  have hm : Measurable (fun x => pd (field K ρ) x a i) :=
    measurable_fderiv_apply_const ℝ (fun x => field K ρ x i) (basis a)
  have hg : LocallyIntegrable (fun _ : Space => D*sourceMass ρ) := continuous_const.locallyIntegrable
  apply hg.mono hm.aestronglyMeasurable
  filter_upwards with x
  exact (coordinate_bound K ρ hρ hd hc D hb hi x a i).trans (by simpa only [Real.norm_eq_abs] using le_abs_self (D*sourceMass ρ))

theorem curl_pairing (K L : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (c : ℂ)
    (hcurl : ∀ x y i j, curl (fun z a => K z y a j) x i=c*L x y i j)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (field K ρ) φ=(fun i => c*(∫ x, field L ρ x i*φ x)) := by
  have hcont (i : Fin 3) : Continuous (fun x => field K ρ x i) :=
    continuous_iff_continuousAt.mpr (fun x => (DensityCurl.differentiable K ρ hρ hd hc D hb hi x i).continuousAt)
  rw [← RadialInterface.curl_integration_by_parts 1 (field K ρ) hcont
    (fun x _ _ i => DensityCurl.differentiable K ρ hρ hd hc D hb hi x i)
    (fun a i => partial_locallyIntegrable K ρ hρ hd hc D hb hi a i) φ hφ hcompact]
  funext i
  simp_rw [DensityCurl.curl_integral K L ρ hρ hd hc D hb hi c hcurl,mul_assoc,integral_const_mul]

end OQ14.DensityWeak
#print axioms OQ14.DensityWeak.coordinate_bound
#print axioms OQ14.DensityWeak.partial_locallyIntegrable
#print axioms OQ14.DensityWeak.curl_pairing
