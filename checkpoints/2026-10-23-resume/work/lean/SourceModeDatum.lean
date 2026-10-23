import SourceDielectricModes
import WeightedFieldEquality
import FreeDyadicMaterialData

/-! Actual free dyadic mode data are the weighted TM and TE vacuum source combination. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceModeDatum
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceDielectricModes OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
abbrev Coefficient := StaticCoefficient.Coefficient

def tmIncident (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) : VectorFourier.VectorL2 :=
  SourceWeightedDatum.datum c d.X hc (vacuum (tmData d (a.1+1))) (representative (a.1+1) a.2)

def teIncident (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) : VectorFourier.VectorL2 :=
  SourceTEWeightedDatum.datum c d.X hc (vacuum (teData d (a.1+1))) (representative (a.1+1) a.2)

theorem annulus_support (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0) :
    ∀ x : Space,x∉WeightedAnnulusDatum.annulus d.R d.X → c.value (VectorFourier.coordinateMap x)=0 := by
  intro x hx
  by_cases hX : x∈closedBall (0 : Space) d.X
  · have hR : x∈ball (0 : Space) d.R := by
      by_contra hn
      exact hx ⟨hX,hn⟩
    exact hi x (mem_ball_zero_iff.mp hR).le
  · exact hc x hX

theorem tm_actual (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => tmIncident c d hc a (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
        SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := by
  filter_upwards [SourceWeightedDatum.actual c d.X hc (vacuum (tmData d (a.1+1)))
    (representative (a.1+1) a.2) hi i] with x hx
  change tmIncident c d hc a (VectorFourier.coordinateMap x) i=_
  unfold tmIncident
  rw [hx,vacuum_electric]
  rfl

theorem te_actual (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => teIncident c d hc a (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
        SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := by
  filter_upwards [SourceTEWeightedDatum.actual c d.X hc (vacuum (teData d (a.1+1)))
    (representative (a.1+1) a.2) hi i] with x hx
  change teIncident c d hc a (VectorFourier.coordinateMap x) i=_
  unfold teIncident
  rw [hx,vacuum_magnetic]
  rfl

theorem mode_eq (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (y : Space) (j : Fin 3) :
    FreeDyadicMaterialData.datum c d.R d.X (fun i => FreeDyadicMaterialData.mode d.R d.X d.hR a y i j)=
      FreeSourceCoefficients.tmCoefficient a y j • tmIncident c d hc a+
        FreeSourceCoefficients.teCoefficient a y j • teIncident c d hc a := by
  apply WeightedFieldEquality.combination c _ _ _
    (fun x i => OutgoingSpatialSeries.term a x y i j)
    (SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2))
    (SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2))
    _ _
    (fun i => FreeDyadicMaterialData.mode_datum_actual c d.R d.X d.hR a y (annulus_support c d hc hi) i j)
    (tm_actual c d hc hi a) (te_actual c d hc hi a)
  intro x i
  rfl

theorem solution_mode_eq (c : Coefficient) (d : Data)
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (hi : ∀ x : Space,‖x‖≤d.R → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (y : Space) (j : Fin 3) :
    MaterialField.solution c 1 d.X
      (FreeDyadicMaterialData.datum c d.R d.X (fun i => FreeDyadicMaterialData.mode d.R d.X d.hR a y i j))=
      FreeSourceCoefficients.tmCoefficient a y j • MaterialField.solution c 1 d.X (tmIncident c d hc a)+
        FreeSourceCoefficients.teCoefficient a y j • MaterialField.solution c 1 d.X (teIncident c d hc a) := by
  rw [mode_eq c d hc hi]
  simp only [MaterialField.solution,map_add,map_smul]

end OQ14.SourceModeDatum
#print axioms OQ14.SourceModeDatum.annulus_support
#print axioms OQ14.SourceModeDatum.tm_actual
#print axioms OQ14.SourceModeDatum.te_actual
#print axioms OQ14.SourceModeDatum.mode_eq
#print axioms OQ14.SourceModeDatum.solution_mode_eq
