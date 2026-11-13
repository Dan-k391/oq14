import Packet05ExplicitLocalizedForcing
import Packet05LocalizedForcingNorm
import Packet05LocalDerivative

/-! Uniqueness exposes the norm of any weak localized forcing derivative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ForcingDerivativeUnique
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ExplicitLocalizedForcing OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05LocalizedForcingNorm OQ14.Packet05DifferenceConverse

theorem localized_forcing_derivative_eq (V : Set Space) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (v Dv : L2Scalar) (F DF J : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (t : Fin 3) (ht : t ≠ 2)
    (hv : HasPartialOn V v Dv t) (hF : ∀ j, HasPartialOn V (F j) (DF j) t)
    (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function) (hζV : tsupport ζ.function ⊆ V)
    (hJ : ∀ j, HasWeakPartial (localizedForcing ζ A v F d hd j) (J j) t) :
    ∀ j, J j = forceDerivative ζ hζ2 A hA v Dv F DF d hd t j := by
  intro j
  exact OQ14.Packet05LocalDerivative.weak_partial_unique
    (localizedForcing ζ A v F d hd j) (J j)
    (forceDerivative ζ hζ2 A hA v Dv F DF d hd t j) t (hJ j)
    (localized_forcing_tangential_derivative_explicit V A hA v Dv F DF d hd t ht hv hF ζ hζ2 hζV j)

end OQ14.Packet05ForcingDerivativeUnique
#print axioms OQ14.Packet05ForcingDerivativeUnique.localized_forcing_derivative_eq
