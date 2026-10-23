import SourceModeInverse
import CoreMaterialEvaluation
import VectorReactionTerms

/-! The literal material response of each free source mode is its normalized vector reaction dyad. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.SourceModeReaction
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceDielectricModes OQ14.SourceModeDatum OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization

def positive (a : PositiveIndex) : SphereHarmonicHilbert.TotalIndex := ⟨a.1+1,a.2⟩

def term (d : Data) (a : PositiveIndex) (x y : Space) (i j : Fin 3) : ℂ :=
  VectorReactionTerms.term true (positive a) i j d.gs d.R d.X d.hR (x,y)+
    VectorReactionTerms.term false (positive a) i j (d.gs.map teLayer) d.R d.X d.hR (x,y)

theorem weight_eq (a : PositiveIndex) :
    DebyeUnitReaction.weight a=(VectorReactionTerms.angularWeight (a.1+1) : ℂ) := by
  simp only [DebyeUnitReaction.weight,VectorReactionTerms.angularWeight,Complex.ofReal_inv,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

theorem tm_normalization (d : Data) (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    FreeSourceCoefficients.tmCoefficient a y j*
      (multiplier (tmData d (a.1+1))*SolidMaxwellProfiles.electric (a.1+1) (representative (a.1+1) a.2) x i)=
      VectorReactionTerms.term true (positive a) i j d.gs d.R d.X d.hR (x,y) := by
  simp only [FreeSourceCoefficients.tmCoefficient,weight_eq]
  dsimp [VectorReactionTerms.term,VectorReactionTerms.product,VectorReactionTerms.component,
    positive,multiplier,tmData,DebyeUnitReaction.electric,SolidMaxwellProfiles.electric]
  ring

theorem te_normalization (d : Data) (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    FreeSourceCoefficients.teCoefficient a y j*
      (multiplier (teData d (a.1+1))*SolidMaxwellProfiles.magnetic (a.1+1) (representative (a.1+1) a.2) x i)=
      VectorReactionTerms.term false (positive a) i j (d.gs.map teLayer) d.R d.X d.hR (x,y) := by
  simp only [FreeSourceCoefficients.teCoefficient,weight_eq]
  dsimp [VectorReactionTerms.term,VectorReactionTerms.product,VectorReactionTerms.component,
    positive,multiplier,teData,DebyeUnitReaction.toroidal,SolidMaxwellProfiles.magnetic,DebyeMaxwell.tmMagnetic]
  ring_nf
  simp only [Complex.I_sq,Complex.I_pow_three]
  ring

theorem mode_core (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (x y : Space) (hx : ‖x‖<d.R) (i j : Fin 3) :
    (∑ h : Fin 3, ∫ z : Space, DynamicVolume.source c
      (MaterialField.solution c 1 d.X
        (FreeDyadicMaterialData.datum c d.R d.X (fun h => FreeDyadicMaterialData.mode d.R d.X d.hR a y h j))) h z*
          DyadicKernel.dyadic 1 (x-z) i h)=term d a x y i j := by
  rw [←CoreMaterialEvaluation.evaluation_actual c d.R d.X (annulus_support c d hc hi) x hx i,
    solution_mode_eq c d hc hi a y j,map_add,map_smul,map_smul,
    CoreMaterialEvaluation.evaluation_actual,CoreMaterialEvaluation.evaluation_actual,
    SourceModeInverse.tm_core c d hm hdisp hu hc a x hx i,
    SourceModeInverse.te_core c d hm hdisp hu hc a x hx i]
  exact congrArg₂ (fun z w : ℂ => z+w) (tm_normalization d a x y i j) (te_normalization d a x y i j)

end OQ14.SourceModeReaction
#print axioms OQ14.SourceModeReaction.weight_eq
#print axioms OQ14.SourceModeReaction.tm_normalization
#print axioms OQ14.SourceModeReaction.te_normalization
#print axioms OQ14.SourceModeReaction.mode_core
