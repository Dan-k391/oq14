import DilationVolume
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ComplexDilationVolume
open Complex MeasureTheory Metric Set Filter OQ14.FrequencyScalingMaxwell OQ14.DilationL2
open scoped Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem scaleCoeff_mul (s t : ℝ) (c : Coefficient) :
    scaleCoeff s (scaleCoeff t c) = scaleCoeff (s*t) c := by
  cases c
  simp [scaleCoeff, ← mul_smul, mul_comm]

theorem scaleCoeff_one (c : Coefficient) : scaleCoeff 1 c = c := by
  cases c
  simp [scaleCoeff]

theorem real_comp (s t R : ℝ) (hs : 0 < s) (ht : 0 < t) (c : Coefficient) :
    DynamicVolume.volumeBlock (scaleCoeff s c) (s*t) (R/s) ∘L dilate s =
      dilate s ∘L DynamicVolume.volumeBlock c t R := by
  let c0 := scaleCoeff t⁻¹ c
  have hcoeff : scaleCoeff t c0 = c := by
    dsimp [c0]; rw [scaleCoeff_mul, mul_inv_cancel₀ ht.ne', scaleCoeff_one]
  have hcoeff2 : scaleCoeff (s*t) c0 = scaleCoeff s c := by
    dsimp [c0]; rw [scaleCoeff_mul]; congr 1; field_simp
  have hrad : (t*R)/(s*t) = R/s := by field_simp; ring
  have hrad2 : (t*R)/t = R := by field_simp
  have h1 := DilationVolume.volumeBlock_comp_dilate (s*t) (t*R) (mul_pos hs ht) c0
  have h2 := DilationVolume.volumeBlock_comp_dilate t (t*R) ht c0
  rw [hcoeff2, hrad] at h1
  rw [hcoeff, hrad2] at h2
  apply ContinuousLinearMap.ext
  intro u
  let v := dilate t⁻¹ u
  have hv : dilate t v = u := by
    dsimp [v]; rw [dilate_mul t t⁻¹ ht (inv_pos.mpr ht), mul_inv_cancel₀ ht.ne', dilate_one]; rfl
  have ha := congrFun (congrArg DFunLike.coe h1) v
  have hb := congrFun (congrArg DFunLike.coe h2) v
  dsimp only [ContinuousLinearMap.comp_apply] at ha hb ⊢
  rw [← dilate_mul s t hs ht, hv] at ha
  rw [← hv, hb]
  simpa only [dilate_mul s t hs ht, hv] using ha

def left (s R : ℝ) (c : Coefficient) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) ∘L dilate s

def right (s R : ℝ) (c : Coefficient) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  dilate s ∘L ComplexConvolutionAnalytic.volumeBlock c z R

theorem left_analytic (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    AnalyticAt ℂ (left s R c) z := by
  have hd := (ComplexConvolutionAnalytic.volumeBlock_differentiable (scaleCoeff s c) (R/s)
    (div_nonneg hR hs.le)).comp ((differentiable_const (s : ℂ)).mul differentiable_id)
  exact (hd.clm_comp (differentiable_const (dilate s))).analyticAt z

theorem right_analytic (s R : ℝ) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    AnalyticAt ℂ (right s R c) z :=
  ((differentiable_const (dilate s)).clm_comp
    (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)).analyticAt z

theorem complex_comp (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) ∘L dilate s =
      dilate s ∘L ComplexConvolutionAnalytic.volumeBlock c z R := by
  have heq (t : ℝ) (ht : 0 < t) : left s R c t = right s R c t := by
    unfold left right
    rw [← Complex.ofReal_mul, ComplexConvolutionAnalytic.volumeBlock_ofReal,
      ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact real_comp s t R hs ht c
  have hclosure : (1 : ℂ) ∈ closure ({w | left s R c w = right s R c w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1+ε/2
    have hr : 0 < r := by dsimp [r]; linarith
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨heq r hr, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ (left s R c) Set.univ from fun w _ => left_analytic s R hs hR c w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => right_analytic s R hR c w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem volumeBlock_eq_conj (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) =
      dilate s * ComplexConvolutionAnalytic.volumeBlock c z R * dilate s⁻¹ := by
  have h : ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) * dilate s =
      dilate s * ComplexConvolutionAnalytic.volumeBlock c z R := complex_comp s R hs hR c z
  have hDE : dilate s * dilate s⁻¹ = 1 := dilate_comp_inv s hs
  calc ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s)
      = ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) *
          (dilate s * dilate s⁻¹) := by rw [hDE, mul_one]
    _ = (ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) *
          dilate s) * dilate s⁻¹ := by rw [mul_assoc]
    _ = _ := by rw [h]

theorem volumeBlock_isUnit_iff (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    IsUnit (ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s)) ↔
      IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R) := by
  rw [volumeBlock_eq_conj s R hs hR c z]
  exact DilationVolume.isUnit_conj_iff _ _ _ (dilate_comp_inv s hs) (dilate_inv_comp s hs)

theorem inverse_eq_conj (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient) (z : ℂ) :
    Ring.inverse (ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s)) =
      dilate s * Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R) * dilate s⁻¹ := by
  rw [volumeBlock_eq_conj s R hs hR c z]
  exact DilationVolume.ring_inverse_conj _ _ _ (dilate_comp_inv s hs) (dilate_inv_comp s hs)

theorem coefficient_support (s R : ℝ) (hs : 0 < s) (c : Coefficient)
    (hc : ∀ x : FourierL2.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (x : FourierL2.Space) (hx : x ∉ closedBall 0 (R/s)) :
    (scaleCoeff s c).value (VectorFourier.coordinateMap x) = 0 := by
  rw [scaleCoeff_value, ← DilationL2.coordinateMap_smul']
  apply hc
  exact fun h => hx ((DilationVolume.mem_closedBall_div_iff s R hs x).mpr h)

theorem nonzero_kernel_transport (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R) (c : Coefficient)
    (z : ℂ) (u : VectorL2) (hu : u ≠ 0)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    dilate s u ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) (dilate s u) = 0 := by
  constructor
  · intro hz
    have hi := congrFun (congrArg DFunLike.coe (dilate_inv_comp s hs)) u
    change dilate s⁻¹ (dilate s u) = u at hi
    rw [hz, map_zero] at hi
    exact hu hi.symm
  · have h := congrFun (congrArg DFunLike.coe (complex_comp s R hs hR c z)) u
    change ComplexConvolutionAnalytic.volumeBlock (scaleCoeff s c) ((s : ℂ)*z) (R/s) (dilate s u) =
      dilate s (ComplexConvolutionAnalytic.volumeBlock c z R u) at h
    rw [hker, map_zero] at h
    exact h

#print axioms OQ14.ComplexDilationVolume.nonzero_kernel_transport
#print axioms OQ14.ComplexDilationVolume.coefficient_support
#print axioms OQ14.ComplexDilationVolume.inverse_eq_conj
#print axioms OQ14.ComplexDilationVolume.volumeBlock_isUnit_iff
#print axioms OQ14.ComplexDilationVolume.complex_comp
#print axioms OQ14.ComplexDilationVolume.real_comp
end OQ14.ComplexDilationVolume




