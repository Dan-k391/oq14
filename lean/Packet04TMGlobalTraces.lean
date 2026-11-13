import Packet04TMDielectric
import ComplexSmoothRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04TMGlobalTraces
open Complex MeasureTheory Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments
open scoped Topology

/-- Global continuous radial representatives and their exact weak increments. -/
theorem actual_global_representatives (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0) :
    ∃ U V : ℝ → ℂ, ContinuousOn U (Ioo (0 : ℝ) T) ∧ ContinuousOn V (Ioo (0 : ℝ) T) ∧
      (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] U ∧
      (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] V ∧
      (∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → U d - U c =
        ∫ r in c..d, (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r) ∧
      (∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → V d - V c =
        ∫ r in c..d, (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
          z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) := by
  let Ω := Ioo (0 : ℝ) T
  have hsub : Ω ⊆ Ioi (0 : ℝ) := fun _ hr => hr.1
  have hD := (displacementRadial_local n hn z T u p).mono_set hsub
  have hDr := (Packet01MomentIntegrability.tangentialMoment_locallyIntegrableOn
    (displacementCoordinates n hn z T u) p l).mono_set hsub
  have hEr := (Packet01MomentIntegrability.radialMoment_locallyIntegrableOn
    (electricCoordinates n hn z T u) p).mono_set hsub
  have hEt := (Packet01MomentIntegrability.tangentialMoment_locallyIntegrableOn
    (electricCoordinates n hn z T u) p l).mono_set hsub
  have hU : LocallyIntegrableOn (fun r : ℝ => (r : ℂ)^2 * displacementRadial n hn z T u p r) Ω :=
    hD.continuousOn_mul (Complex.continuous_ofReal.pow 2).continuousOn isOpen_Ioo.isLocallyClosed
  have hUd : LocallyIntegrableOn (fun r : ℝ => (r : ℂ) *
      tangentialMoment (displacementCoordinates n hn z T u) p l r) Ω :=
    hDr.continuousOn_mul Complex.continuous_ofReal.continuousOn isOpen_Ioo.isLocallyClosed
  have hV : LocallyIntegrableOn (fun r : ℝ => (r : ℂ) *
      tangentialMoment (electricCoordinates n hn z T u) p l r) Ω :=
    hEt.continuousOn_mul Complex.continuous_ofReal.continuousOn isOpen_Ioo.isLocallyClosed
  have hVd : LocallyIntegrableOn (fun r : ℝ => (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
      z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) Ω := by
    have h1 := hEr.continuousOn_mul (show ContinuousOn (fun _ : ℝ => (l+1 : ℂ)*(l+2 : ℂ)) Ω from continuousOn_const)
      isOpen_Ioo.isLocallyClosed
    have h2 := hU.continuousOn_mul (show ContinuousOn (fun _ : ℝ => z^2) Ω from continuousOn_const)
      isOpen_Ioo.isLocallyClosed
    convert h1.sub h2 using 1
    ext r
    simp only [Pi.sub_apply, electricRadial]
    ring
  obtain ⟨U,hUc,hUae,hUi⟩ := ComplexSmoothRepresentative.representative isOpen_Ioo _ _ hU hUd
    (Packet04TMFirstDerivative.actual_first_weak_derivative n hn z hz T hT u hker p l hp)
  obtain ⟨V,hVc,hVae,hVi⟩ := ComplexSmoothRepresentative.representative isOpen_Ioo _ _ hV hVd
    (Packet04TMSecondDerivative.actual_second_weak_derivative n hn z T hT u hker p l hp hh)
  exact ⟨U,V,hUc,hVc,hUae,hVae,hUi,hVi⟩

#print axioms OQ14.Packet04TMGlobalTraces.actual_global_representatives
end OQ14.Packet04TMGlobalTraces
