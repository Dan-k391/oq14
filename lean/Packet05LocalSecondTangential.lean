import Packet05LocalizedGradientPlateau

/-! Second tangential derivatives produced by nested scalar iteration are
genuine local derivatives of the original tangential-gradient derivatives. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05LocalSecondTangential
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05LocalizedGradientPlateau

theorem nested_to_local_second (W : Set Space) (hW : IsOpen W)
    (κ ζ : RealTest Set.univ) (hκ : ∀ x ∈ W, κ.function x = 1)
    (hζ : ∀ x ∈ W, ζ.function x = 1) (v : L2Scalar) (G : L2Vector)
    (j t : Fin 3) (H : L2Scalar)
    (hH : HasWeakPartial
      (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
        (localizedGradient κ v G j)) H t) :
    HasPartialOn W (G j) H t := by
  have hζc : ∀ x ∈ W, ζ.complexTest.function x = 1 := by
    intro x hx
    simp [RealTest.complexTest,hζ x hx]
  have hl := cutoff_partial_on W ζ.complexTest.toTest (localizedGradient κ v G j) H t hζc hH
  apply partial_on_of_ae_eq W (G j) (localizedGradient κ v G j) H t hl
  filter_upwards [localized_gradient_plateau W hW κ hκ v G j] with x hx hW
  exact (hx hW).symm

end OQ14.Packet05LocalSecondTangential
#print axioms OQ14.Packet05LocalSecondTangential.nested_to_local_second
