import Packet05ActualTransmissionContinuous
import Packet05RegionalBootstrappedScalar
import Packet05LocalizedGradientPlateau

/-! The compact bootstrapped scalar variables agree with the original
regional variables on the localization plateau. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05BootstrapRepresentativeTransfer
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05LocalizedGradientPlateau

theorem bootstrap_representatives_on_plateau (T : Set Space) (hT : IsOpen T)
    (κ : RealTest Set.univ) (hκ : ∀ x ∈ T, κ.function x = 1)
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (f0 f1 fn : Space → ℂ)
    (h0 : (localizedGradient κ u C 0 : Space → ℂ) =ᵐ[volume.restrict T] f0)
    (h1 : (localizedGradient κ u C 1 : Space → ℂ) =ᵐ[volume.restrict T] f1)
    (hn : (fun x => (flux A (localizedGradient κ u C) d hd 2-
      localizedForcing κ A u F d hd 2 : L2Scalar) x) =ᵐ[volume.restrict T] fn) :
    (C 0 : Space → ℂ) =ᵐ[volume.restrict T] f0 ∧
    (C 1 : Space → ℂ) =ᵐ[volume.restrict T] f1 ∧
    (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] fn := by
  have hG (j : Fin 3) : (localizedGradient κ u C j : Space → ℂ) =ᵐ[volume.restrict T] (C j : Space → ℂ) :=
    (ae_restrict_iff' hT.measurableSet).mpr (localized_gradient_plateau T hT κ hκ u C j)
  refine ⟨(hG 0).symm.trans h0,(hG 1).symm.trans h1,?_⟩
  have heq := localized_scalar_flux_identity κ A u C F d hd 2
  rw [heq] at hn
  filter_upwards [hn,ae_restrict_of_ae (cutScalar_ae κ (flux A C d hd 2-F 2)),
    ae_restrict_mem hT.measurableSet] with x hn hx hxt
  change cutScalar κ (flux A C d hd 2-F 2) x = fn x at hn
  rw [hx,hκ x hxt] at hn
  simpa using hn

end OQ14.Packet05BootstrapRepresentativeTransfer
#print axioms OQ14.Packet05BootstrapRepresentativeTransfer.bootstrap_representatives_on_plateau
