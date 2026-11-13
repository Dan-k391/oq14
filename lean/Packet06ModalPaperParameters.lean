import Packet06ModalHotspotExistence

/-! The modal existence theorem with the paper's permittivity ceiling and
strict observation diameter, and explicit global-field identification. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06ModalPaperParameters
open MeasureTheory Maxwell Packet06ModalHotspotExistence

theorem exists_modal_packing (N : ℕ) (ε target Q ℓ M : ℝ)
    (hε : 1 < ε) (htarget : 0 < target) (hQ : 0 ≤ Q) (hℓ : 0 < ℓ)
    (P : Set Plane) (hPopen : IsOpen P) (hP : P.Nonempty) :
    ∃ d : Device N, Valid d (Real.sqrt ε) target Q (ℓ/4) M P ∧
      (∀ x, 1 ≤ MaterialMaxwell.dielectric d.material x ∧ MaterialMaxwell.dielectric d.material x ≤ ε) ∧
      2*d.radius < ℓ ∧
      ∀ k, (fun x => Packet06GlobalField.electric d.material d.frequency d.supportRadius d.unknown x k)
        =ᵐ[volume] (fun x => Packet06ComplexElectric.electric d.frequency
          (StaticCoefficient.sqrtMultiplier d.material d.unknown)
          (DynamicVolume.source d.material d.unknown) x k) := by
  have hε0 : 0 ≤ ε := le_trans zero_le_one hε.le
  have hK : 1 < Real.sqrt ε := by
    have hs := Real.sq_sqrt hε0
    have hp := Real.sqrt_nonneg ε
    nlinarith
  obtain ⟨d,hd⟩ := exists_modal_hotspots N (Real.sqrt ε) target Q (ℓ/4) M hK htarget hQ
    (by positivity) P hPopen hP
  refine ⟨d,hd,?_,?_,?_⟩
  · intro x
    simpa only [Real.sq_sqrt hε0] using hd.material_bounds x
  · have hh := hd.radius_bound
    linarith
  · exact Packet06GlobalElectricIdentification.global_electric_ae d.material d.frequency d.supportRadius d.unknown hd.material_support

end OQ14.Packet06ModalPaperParameters
#print axioms OQ14.Packet06ModalPaperParameters.exists_modal_packing
