import HalfTurnReactionBridge

/-! The central-equals-wall identity of the proper-half-turn-invariant sector holds for sources that
are invariant only almost everywhere, since the invariance enters under an integral. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.HalfTurnReactionBridgeAE
open MeasureTheory OQ14.Maxwell OQ14.SphereReactionKernel OQ14.HalfTurnMaxwellParity
open OQ14.HalfTurnReactionKernel OQ14.HalfTurnReactionBridge
abbrev Space := Maxwell.Space

/-- Almost-everywhere proper-half-turn invariance of a source field. -/
def InvariantAE (ρ : Field) : Prop := ∀ j : Fin 3, ∀ᵐ y : Space, ρ (halfTurn y) j= -(sign j : ℂ)*ρ y j

theorem invariantAE_of_invariant (ρ : Field) (h : Invariant ρ) : InvariantAE ρ :=
  fun j => Filter.Eventually.of_forall (fun y => h y j)

theorem potential_invariant_ae (k : ℝ) (ρ : Field) (hρ : InvariantAE ρ) : Invariant (potential k ρ) := by
  intro x i
  change (∑ j : Fin 3, ∫ y : Space, J k (halfTurn x-y) i j*ρ y j)=_
  have he (j : Fin 3) : (∫ y : Space, J k (halfTurn x-y) i j*ρ y j)=
      -(sign i : ℂ)*(∫ y : Space, J k (x-y) i j*ρ y j) := by
    have hc := HarmonicHalfTurn.rotation.measurePreserving.integral_comp
      HarmonicHalfTurn.rotation.toHomeomorph.measurableEmbedding
      (fun y : Space => J k (halfTurn x-y) i j*ρ y j)
    rw [←hc,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hρ j] with y hy
    rw [←rotation_eq,←map_sub,J_rotation,rotation_eq,hy]
    have hs : (sign j : ℂ)^2=1 := by unfold sign; split_ifs <;> norm_num
    linear_combination -((sign i : ℂ)*J k (x-y) i j*ρ y j)*hs
  simp_rw [he]
  rw [←Finset.mul_sum]
  rfl

theorem central_eq_wall_ae (e : Bool) (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (hs : InvariantAE ρ) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, central e k x y i j*ρ y j)=
      ∑ j : Fin 3, ∫ y : Space, reaction e k x y i j*ρ y j := by
  rw [central_integral e k ρ hρ,wall_integral e k ρ hρ,
    inversion_wall _ (potential_invariant_ae k ρ hs)]
  cases e <;> simp

end OQ14.HalfTurnReactionBridgeAE
#print axioms OQ14.HalfTurnReactionBridgeAE.invariantAE_of_invariant
#print axioms OQ14.HalfTurnReactionBridgeAE.potential_invariant_ae
#print axioms OQ14.HalfTurnReactionBridgeAE.central_eq_wall_ae
