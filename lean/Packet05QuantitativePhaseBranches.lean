import Packet05PhysicalReconstructionBound
import Packet05BootstrapRepresentativeTransfer
import Packet05GraphTransmissionReconstruction

/-! Construct actual continuous physical-field branches on each constant
phase from the derived graph transmission representatives. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativePhaseBranches
open MeasureTheory Set OQ14.Maxwell OQ14.Packet05GraphTransmissionReconstruction

theorem quantitative_phase_branches (T : Set Space) (E : Field) (ε : ℂ) (hε : ε ≠ 0)
    (a b : Space → ℝ) (ha : Continuous a) (hb : Continuous b)
    (C0 C1 C2 N w0 w1 w2 : Space → ℂ)
    (f0 f1 fn : Space → ℂ) (hf0 : Continuous f0) (hf1 : Continuous f1) (hfn : Continuous fn)
    (hw0 : Continuous w0) (hw1 : Continuous w1) (hw2 : Continuous w2)
    (hC0 : C0 =ᵐ[volume.restrict T] f0) (hC1 : C1 =ᵐ[volume.restrict T] f1)
    (hN : N =ᵐ[volume.restrict T] fn)
    (hflux : ∀ᵐ x ∂volume.restrict T, N x = ε *
      (-(a x : ℂ)*C0 x-(b x : ℂ)*C1 x + ((1+(a x)^2+(b x)^2 : ℝ) : ℂ)*C2 x +
        w2 x-(a x : ℂ)*w0 x-(b x : ℂ)*w1 x))
    (hE0 : ∀ᵐ x ∂volume.restrict T, E x 0 = C0 x-(a x : ℂ)*C2 x+w0 x)
    (hE1 : ∀ᵐ x ∂volume.restrict T, E x 1 = C1 x-(b x : ℂ)*C2 x+w1 x)
    (hE2 : ∀ᵐ x ∂volume.restrict T, E x 2 = C2 x+w2 x)
    (M K X : ℝ) (hM : 0 ≤ M) (hK : ‖ε⁻¹‖ ≤ K)
    (hab : ∀ x ∈ T, |a x| ≤ M ∧ |b x| ≤ M)
    (hdata : ∀ x ∈ T, ‖f0 x‖ ≤ X ∧ ‖f1 x‖ ≤ X ∧ ‖fn x‖ ≤ X ∧
      ‖w0 x‖ ≤ X ∧ ‖w1 x‖ ≤ X ∧ ‖w2 x‖ ≤ X) :
    ∃ reps : Fin 3 → Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict T] reps j) ∧
      ∀ j x, x ∈ T → ‖reps j x‖ ≤ (2+(1+M)*(K+4*M+1))*X := by
  let reps : Fin 3 → Space → ℂ := fun j x => physicalField (a x) (b x) ε
    (f0 x) (f1 x) (fn x) (w0 x) (w1 x) (w2 x) j
  refine ⟨reps,?_,?_,?_⟩
  · intro j
    exact reconstructed_field_continuous a b ε f0 f1 fn w0 w1 w2 ha hb hf0 hf1 hfn hw0 hw1 hw2 j
  · intro j
    filter_upwards [hC0,hC1,hN,hflux,hE0,hE1,hE2] with x h0 h1 hn hp he0 he1 he2
    have hnormal : normalGradient (a x) (b x) ε (f0 x) (f1 x) (fn x)
        (w0 x) (w1 x) (w2 x) = C2 x := by
      rw [← h0,← h1,← hn,hp]
      exact normal_gradient_recovery (a x) (b x) ε (C0 x) (C1 x) (C2 x) (w0 x) (w1 x) (w2 x) hε
    fin_cases j
    · change E x 0 = f0 x-(a x : ℂ)*normalGradient (a x) (b x) ε (f0 x) (f1 x) (fn x) (w0 x) (w1 x) (w2 x)+w0 x
      rw [hnormal,← h0]
      exact he0
    · change E x 1 = f1 x-(b x : ℂ)*normalGradient (a x) (b x) ε (f0 x) (f1 x) (fn x) (w0 x) (w1 x) (w2 x)+w1 x
      rw [hnormal,← h1]
      exact he1
    · change E x 2 = normalGradient (a x) (b x) ε (f0 x) (f1 x) (fn x) (w0 x) (w1 x) (w2 x)+w2 x
      rw [hnormal]
      exact he2
  · intro j x hx
    obtain ⟨ha,hb⟩ := hab x hx
    obtain ⟨h0,h1,hn,hw0,hw1,hw2⟩ := hdata x hx
    exact Packet05PhysicalReconstructionBound.physical_field_norm (a x) (b x) ε
      (f0 x) (f1 x) (fn x) (w0 x) (w1 x) (w2 x) M K X hM hK ha hb
      h0 h1 hn hw0 hw1 hw2 j

end OQ14.Packet05QuantitativePhaseBranches
#print axioms OQ14.Packet05QuantitativePhaseBranches.quantitative_phase_branches
