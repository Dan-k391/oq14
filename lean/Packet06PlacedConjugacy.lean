import Packet06PlacedEquivalence

/-! The actual full complex volume block conjugates under the placed L2 equivalence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06PlacedConjugacy
open Metric Maxwell Packet06PlacedKernel Packet06PlacedEquivalence

theorem volume_intertwines (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : V) :
    ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z)
      (R/s+‖a‖) (placed s hs a u) =
      placed s hs a (ComplexConvolutionAnalytic.volumeBlock c z R u) := by
  let cr := Packet06CyclicMaterial.coefficient c
  let cd := FrequencyScalingMaxwell.scaleCoeff s cr
  have hcr : ∀ x : Space, x ∉ closedBall 0 R → cr.value (VectorFourier.coordinateMap x)=0 :=
    Packet06CyclicDynamic.coefficient_support c R hc
  have hcd : ∀ x : Space, x ∉ closedBall 0 (R/s) → cd.value (VectorFourier.coordinateMap x)=0 :=
    ComplexDilationVolume.coefficient_support s R hs cr hcr
  have hC := congrArg (fun A : V →L[ℂ] V => A u)
    (Packet06CyclicComplex.complex_conjugacy c R hR hc z)
  change ComplexConvolutionAnalytic.volumeBlock cr z R (Packet06CyclicL2.action u) =
    Packet06CyclicL2.action (ComplexConvolutionAnalytic.volumeBlock c z R u) at hC
  have hD := congrArg (fun A : V →L[ℂ] V => A (Packet06CyclicL2.action u))
    (ComplexDilationVolume.complex_comp s R hs hR cr z)
  change ComplexConvolutionAnalytic.volumeBlock cd ((s : ℂ)*z) (R/s)
    (DilationL2.dilate s (Packet06CyclicL2.action u)) =
    DilationL2.dilate s (ComplexConvolutionAnalytic.volumeBlock cr z R (Packet06CyclicL2.action u)) at hD
  have hT := congrArg (fun A : V →L[ℂ] V => A
    ((Real.sqrt s : ℂ) • DilationL2.dilate s (Packet06CyclicL2.action u)))
    (Packet06TranslationComplex.complex_conjugacy a cd (R/s) (div_nonneg hR hs.le) hcd ((s : ℂ)*z))
  change ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z) (R/s+‖a‖)
    (placedUnknown s a u) = Packet06TranslationL2.action a
      (ComplexConvolutionAnalytic.volumeBlock cd ((s : ℂ)*z) (R/s)
        ((Real.sqrt s : ℂ) • DilationL2.dilate s (Packet06CyclicL2.action u))) at hT
  rw [placed_apply,hT,map_smul,hD,hC]
  rfl

theorem volume_conjugacy (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    (placed s hs a).symm.toContinuousLinearMap.comp
      ((ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖)).comp (placed s hs a).toContinuousLinearMap) =
      ComplexConvolutionAnalytic.volumeBlock c z R := by
  apply ContinuousLinearMap.ext
  intro u
  change (placed s hs a).symm
    (ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z)
      (R/s+‖a‖) (placed s hs a u)) = _
  rw [volume_intertwines c R hR hc s hs a z u,ContinuousLinearEquiv.symm_apply_apply]

theorem static_intertwines (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (u : V) :
    StaticNewton.volumeBlock (placedCoefficient s a c) (placed s hs a u) =
      placed s hs a (StaticNewton.volumeBlock c u) := by
  simpa only [mul_zero,ComplexConvolutionAnalytic.volumeBlock,
    ComplexConvolutionAnalytic.weightedRemainder_zero,sub_zero] using
    volume_intertwines c R hR hc s hs a 0 u

theorem pencil_intertwines (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : V) :
    ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) ((s : ℂ)*z)
      (R/s+‖a‖) (placed s hs a u) =
      placed s hs a (ComplexConvolutionAnalytic.pencil c z R u) := by
  let B := StaticNewton.volumeBlock (placedCoefficient s a c)
  have hfactor (d : StaticCoefficient.Coefficient) (w : ℂ) (S : ℝ) (v : V) :
      StaticNewton.volumeBlock d (ComplexConvolutionAnalytic.pencil d w S v) =
        ComplexConvolutionAnalytic.volumeBlock d w S v :=
    congrArg (fun A : V →L[ℂ] V => A v) (ComplexConvolutionAnalytic.volumeBlock_factor d w S).symm
  have he : B (ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖) (placed s hs a u)) =
      B (placed s hs a (ComplexConvolutionAnalytic.pencil c z R u)) := by
    dsimp only [B]
    rw [hfactor,volume_intertwines c R hR hc s hs a z u,
      static_intertwines c R hR hc s hs a _,hfactor]
  have hInv (v : V) : Ring.inverse B (B v)=v := by
    change (Ring.inverse B*B) v=v
    rw [Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit _)]
    rfl
  simpa only [hInv] using congrArg (fun v : V => Ring.inverse B v) he

end OQ14.Packet06PlacedConjugacy
#print axioms OQ14.Packet06PlacedConjugacy.volume_intertwines
#print axioms OQ14.Packet06PlacedConjugacy.volume_conjugacy
#print axioms OQ14.Packet06PlacedConjugacy.static_intertwines
#print axioms OQ14.Packet06PlacedConjugacy.pencil_intertwines
