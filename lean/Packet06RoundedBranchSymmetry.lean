import Packet06ActualAxialAmplitude
import Packet06RoundedPhaseRotation
import Packet05PhaseRepresentativeSymmetry

/-! Actual one-sided amplitudes inherit axial symmetry on open observation
neighborhoods, including their genuine material boundary traces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedBranchSymmetry
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06ConcreteModalRounding
abbrev Space := Maxwell.Space

def phaseOpen (B : Set Space) : Bool → Set Space
  | true => B
  | false => (closure B)ᶜ

theorem phaseDomain_eq (B : Set Space) (b : Bool) : phaseDomain B b=closure (phaseOpen B b) := by
  cases b <;> rfl

theorem branch_symmetry {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) (j : ℕ)
    (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 u=0)
    (K V : Set Space) (hV : IsOpen V) (hVK : V ⊆ K) (hVball : V ⊆ ball (0 : Space) 1)
    (hrotV : ∀ θ, MapsTo (rotation θ) V V)
    (b : Bool) (R : Fin 3 → Space → ℂ)
    (hR : ∀ i, ContinuousOn (R i) (K ∩ phaseDomain (body g j) b))
    (hAE : ∀ i, (fun x => Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) u)
        (DynamicVolume.source (rounded n hn g η hη j) u) x i)
      =ᵐ[volume.restrict (K ∩ phaseOpen (body g j) b)] R i) :
    ∀ θ x, x ∈ V ∩ phaseDomain (body g j) b →
      physicalAmplitude R (rotation θ x)=physicalAmplitude R x := by
  let U := phaseOpen (body g j) b
  let E := Packet06ComplexElectric.electric z
    (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) u)
    (DynamicVolume.source (rounded n hn g η hη j) u)
  have hopen : IsOpen U := by
    cases b
    · exact isClosed_closure.isOpen_compl
    · exact CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hrotU (θ : ℝ) : MapsTo (rotation θ) U U := by
    intro x hx
    cases b
    · exact (not_congr (Packet06RoundedPhaseRotation.closure_rotation (body g j)
        (Packet06RoundedPhaseRotation.body_rotation g j) θ x)).mpr hx
    · exact (Packet06RoundedPhaseRotation.body_rotation g j θ x).mpr hx
  have hcont : ContinuousOn (physicalAmplitude R) (closure U ∩ V) := by
    apply (amplitude_continuousOn R _ hR).mono
    intro x hx
    exact ⟨hVK hx.2,(phaseDomain_eq (body g j) b).symm ▸ hx.1⟩
  have hfa : physicalAmplitude R =ᵐ[volume.restrict (U ∩ V)]
      physicalAmplitude (fun i y => E y i) := by
    have hsub : U ∩ V ⊆ K ∩ phaseOpen (body g j) b := fun x hx => ⟨hVK hx.2,hx.1⟩
    have he : ∀ᵐ x ∂volume.restrict (U ∩ V), ∀ i, E x i=R i x :=
      ae_restrict_of_ae_restrict_of_subset hsub (ae_all_iff.mpr hAE)
    filter_upwards [he] with x hx
    simp only [physicalAmplitude]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hx i])
  intro θ x hx
  have hae : (physicalAmplitude (fun i y => E y i) ∘ rotation θ)
      =ᵐ[volume.restrict V] physicalAmplitude (fun i y => E y i) :=
    ae_restrict_of_ae_restrict_of_subset hVball
      (Packet06ActualAxialAmplitude.rounded_amplitude_ae n hn g η hη j z u hu θ)
  exact Packet05PhaseRepresentativeSymmetry.representative_symmetry U V hopen hV
    (physicalAmplitude R) (physicalAmplitude (fun i y => E y i)) hcont (rotation θ)
    (rotation θ).continuous (rotation θ).measurePreserving (hrotU θ) (hrotV θ) hfa hae
    ⟨(phaseDomain_eq (body g j) b) ▸ hx.2,hx.1⟩

end OQ14.Packet06RoundedBranchSymmetry
#print axioms OQ14.Packet06RoundedBranchSymmetry.phaseDomain_eq
#print axioms OQ14.Packet06RoundedBranchSymmetry.branch_symmetry
