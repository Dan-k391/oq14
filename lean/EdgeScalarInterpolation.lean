import EdgeCosineJets
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-! Genuine finite symmetric scalar plane-wave jet interpolation at distinct edge points. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EdgeScalarInterpolation
open Set
variable {ι : Type*} [Fintype ι]
abbrev Jet (ι : Type*) := (ι × Fin 6) → ℂ

def scalarJet (r : ℝ) (y : ι → ℝ) (s t : ℂ) : Jet ι := fun p =>
  let θ := (r : ℂ)*s+(y p.1 : ℂ)*t
  match p.2.val with
  | 0 => Complex.cos θ
  | 1 => -s*Complex.sin θ
  | 2 => -t*Complex.sin θ
  | 3 => -s^2*Complex.cos θ
  | 4 => -s*t*Complex.cos θ
  | _ => -t^2*Complex.cos θ

def Frequency (δ : ℝ) := {p : ℝ × ℝ // -δ < p.1 ∧ p.1 < δ ∧ -δ < p.2 ∧ p.2 < δ}

theorem dual_zero (r : ℝ) (hr : r ≠ 0) (y : ι → ℝ) (hy : Function.Injective y)
    (δ : ℝ) (hδ : 0 < δ) (L : Jet ι →ₗ[ℂ] ℂ)
    (hz : ∀ s t : ℝ, -δ < s → s < δ → -δ < t → t < δ → L (scalarJet r y s t)=0) : L=0 := by
  classical
  let J := fun j n => L (fun p : ι × Fin 6 => if (j,n)=p then 1 else 0)
  have he (s t : ℂ) : L (scalarJet r y s t)=EdgeCosineJets.functional r y J s t := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [Fintype.sum_prod_type,smul_eq_mul]
    unfold EdgeCosineJets.functional
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.sum_univ_six]
    dsimp [scalarJet,J]
    ring
  have hc := EdgeCosineJets.coefficients_zero r hr y hy J δ hδ
    (fun s t hs hs' ht ht' => (he s t).symm.trans (hz s t hs hs' ht ht'))
  have hb (p : ι × Fin 6) : L (fun q => if p=q then 1 else 0)=0 := by
    simpa only [J,Prod.mk.eta] using hc p.1 p.2
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [hb,smul_zero,Finset.sum_const_zero,LinearMap.zero_apply]

theorem span_top (r : ℝ) (hr : r ≠ 0) (y : ι → ℝ) (hy : Function.Injective y) (δ : ℝ) (hδ : 0 < δ) :
    Submodule.span ℂ (range (fun p : Frequency δ => scalarJet r y p.val.1 p.val.2))=⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro L hL
  apply dual_zero r hr y hy δ hδ L
  intro s t hs hs' ht ht'
  exact (Submodule.mem_dualAnnihilator _).mp hL _ (Submodule.subset_span
    (mem_range.mpr ⟨⟨(s,t),hs,hs',ht,ht'⟩,rfl⟩))

theorem finite_interpolant (r : ℝ) (hr : r ≠ 0) (y : ι → ℝ) (hy : Function.Injective y)
    (δ : ℝ) (hδ : 0 < δ) (v : Jet ι) :
    ∃ A : Frequency δ →₀ ℂ,
      Finsupp.linearCombination ℂ (fun p : Frequency δ => scalarJet r y p.val.1 p.val.2) A=v := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  rw [span_top r hr y hy δ hδ]
  trivial

end OQ14.EdgeScalarInterpolation
#print axioms OQ14.EdgeScalarInterpolation.dual_zero
#print axioms OQ14.EdgeScalarInterpolation.span_top
#print axioms OQ14.EdgeScalarInterpolation.finite_interpolant
