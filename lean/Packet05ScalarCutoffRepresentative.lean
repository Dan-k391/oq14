import Packet05ActualNormalFluxContinuous
import Packet05ActualScalarTangentialContinuity

/-! Recover the uncut transmission component on an inner plateau from its
continuous cutoff representative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ScalarCutoffRepresentative
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05ScalarCutoffTransfer

theorem uncut_on_plateau (T : Set Space) (hT : IsOpen T) (κ : RealTest Set.univ) (χ : Test)
    (hκ : ∀ x ∈ T, κ.function x = 1) (hχ : ∀ x ∈ T, χ.function x = 1)
    (u : L2Scalar) (f : Space → ℂ)
    (h : (fun x => scaleL2 χ.function χ.regular.continuous χ.compact (cutScalar κ u) x) =ᵐ[volume] f) :
    (u : Space → ℂ) =ᵐ[volume.restrict T] f := by
  apply (ae_restrict_iff' hT.measurableSet).mpr
  filter_upwards [h, scaleL2_ae χ.function χ.regular.continuous χ.compact (cutScalar κ u),
    cutScalar_ae κ u] with x hf hχ' hκ' hx
  rw [hχ',hκ',hχ x hx,hκ x hx,Complex.ofReal_one,one_mul,one_mul] at hf
  exact hf

end OQ14.Packet05ScalarCutoffRepresentative
#print axioms OQ14.Packet05ScalarCutoffRepresentative.uncut_on_plateau
