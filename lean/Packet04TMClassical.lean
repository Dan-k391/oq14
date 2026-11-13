import Packet04TMGlobalTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04TMClassical
open Complex MeasureTheory Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments OQ14.Packet04TMDielectric
open scoped Topology

/-- On any open positive-radius region of constant permittivity, the actual
continuous TM representatives satisfy the classical first-order system. -/
theorem region_ode (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (J : Set ℝ) (hJ : IsOpen J)
    (hsub : J ⊆ Ioo (0 : ℝ) T) (ε : ℂ) (hε : ε ≠ 0)
    (heps : ∀ r ∈ J, radialPermittivity n r = ε) (U V : ℝ → ℂ)
    (hUc : ContinuousOn U (Ioo (0 : ℝ) T)) (hVc : ContinuousOn V (Ioo (0 : ℝ) T))
    (hU : (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] U)
    (hV : (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] V)
    (hUi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → U d-U c =
      ∫ r in c..d, (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r)
    (hVi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → V d-V c =
      ∫ r in c..d, (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
        z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) :
    (∀ r ∈ J, HasDerivAt U (ε*V r) r) ∧
    (∀ r ∈ J, HasDerivAt V (((l+1 : ℂ)*(l+2 : ℂ)/(ε*(r : ℂ)^2)-z^2)*U r) r) := by
  have hp : J ⊆ Ioi (0 : ℝ) := fun r hr => (hsub hr).1
  have hDr := ae_restrict_of_ae_restrict_of_subset hp
    (displacement_radial_factor n hn z T hT u hker p)
  have hDt := ae_restrict_of_ae_restrict_of_subset hp
    (displacement_tangential_factor n hn z T hT u hker p l)
  have hUa := ae_restrict_of_ae_restrict_of_subset hsub hU
  have hVa := ae_restrict_of_ae_restrict_of_subset hsub hV
  have hrJ : ∀ᵐ r : ℝ ∂volume.restrict J, r ∈ J := ae_restrict_mem hJ.measurableSet
  have hu : (fun r => (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r) =ᵐ[volume.restrict J]
      fun r => ε*V r := by
    filter_upwards [hDt,hVa,hrJ] with r ht hv hr
    rw [ht, heps r hr, ← hv]
    ring
  have hv : (fun r => (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
      z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) =ᵐ[volume.restrict J]
      fun r => ((l+1 : ℂ)*(l+2 : ℂ)/(ε*(r : ℂ)^2)-z^2)*U r := by
    filter_upwards [hDr,hUa,hrJ] with r hd hu hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hp hr))
    rw [← hu]
    simp only [hd, heps r hr]
    field_simp [hε,hr0]
    ring
  have hc1 : ContinuousOn (fun r => ε*V r) J := continuousOn_const.mul (hVc.mono hsub)
  have hden : ContinuousOn (fun r : ℝ => ε*(r : ℂ)^2) J :=
    continuousOn_const.mul (Complex.continuous_ofReal.pow 2).continuousOn
  have hc2 : ContinuousOn (fun r : ℝ => ((l+1 : ℂ)*(l+2 : ℂ)/(ε*(r : ℂ)^2)-z^2)*U r) J := by
    apply ((continuousOn_const.div hden ?_).sub continuousOn_const).mul (hUc.mono hsub)
    intro r hr
    exact mul_ne_zero hε (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hp hr))))
  constructor
  · intro r hr
    exact ComplexSmoothRepresentative.hasDerivAt_of_increment hJ U _ _
      (fun c d hs => hUi c d (hs.trans hsub)) hu hc1 hr
  · intro r hr
    exact ComplexSmoothRepresentative.hasDerivAt_of_increment hJ V _ _
      (fun c d hs => hVi c d (hs.trans hsub)) hv hc2 hr

#print axioms OQ14.Packet04TMClassical.region_ode
end OQ14.Packet04TMClassical
