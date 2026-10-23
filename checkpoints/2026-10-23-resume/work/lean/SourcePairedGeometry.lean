import SourceDielectricModes
import RadialPairedFamily

/-! Literal common dielectric quarter-pair geometry for the actual TM and TE source modes. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourcePairedGeometry
open OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.SourceRadialSystem

def teSegment (g : Segment) : Segment := {g with σ := 1, σ_pos := zero_lt_one}

theorem reset_width (gs : List Segment) : width (gs.map teSegment)=width gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa only [List.map_cons,width,teSegment] using congrArg (fun t => g.width+t) ih

theorem reset_layer (g : Segment) (R : ℝ) (hR : 0<R) :
    SourceDielectricModes.teLayer (g.layer R hR)=(teSegment g).layer R hR := rfl

theorem reset_layers (gs : List Segment) (R : ℝ) (hR : 0<R) :
    (layers gs R hR).map SourceDielectricModes.teLayer=layers (gs.map teSegment) R hR := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [layers,List.map_append,List.map_singleton,List.map_cons,reset_layer]
    exact congrArg (fun s => s++[(teSegment g).layer R hR])
      (ih (R+g.width) (add_pos_of_pos_of_nonneg hR g.width_nonneg))

theorem reset_pairs (q σ : ℝ) (hq : 0<q) (hσ : 0<σ) (n : ℕ) :
    (pairs q σ hq hσ n).map teSegment=pairs q 1 hq zero_lt_one n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh : teSegment (high q σ hq hσ)=high q 1 hq zero_lt_one := rfl
    have hl : teSegment low=low := rfl
    simp only [pairs,List.map_cons,hh,hl,ih]

theorem reset_tm (q : ℝ) (hq : 0<q) (n : ℕ) :
    (RadialPairedFamily.tm q hq n).map teSegment=RadialPairedFamily.te q hq n :=
  reset_pairs q (q^2) hq (sq_pos_of_pos hq) n

theorem paired_width (q : ℝ) (hq : 0<q) (n : ℕ) :
    width (RadialPairedFamily.tm q hq n)=width (RadialPairedFamily.te q hq n) := by
  rw [←reset_tm q hq n,reset_width]

theorem paired_layers (q : ℝ) (hq : 0<q) (n : ℕ) (R : ℝ) (hR : 0<R) :
    (layers (RadialPairedFamily.tm q hq n) R hR).map SourceDielectricModes.teLayer=
      layers (RadialPairedFamily.te q hq n) R hR := by
  rw [reset_layers,reset_tm]

theorem tm_dispersion (q : ℝ) (hq : 0<q) (n : ℕ) :
    ∀ g∈RadialPairedFamily.tm q hq n,g.q^2=g.σ := by
  induction n with
  | zero => simp only [RadialPairedFamily.tm,pairs,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ n ih =>
    intro g hg
    simp only [RadialPairedFamily.tm,pairs,List.mem_cons] at hg
    rcases hg with rfl|rfl|hg
    · rfl
    · norm_num [low]
    · exact ih g hg

def physicalData (q : ℝ) (hq : 0<q) (n r : ℕ) : Data where
  l := 0
  gs := layers (RadialPairedFamily.tm q hq n) (radius r) (radius_pos r)
  R := radius r
  X := radius r+width (RadialPairedFamily.tm q hq n)
  c := radius r/4
  hR := radius_pos r
  hc := div_pos (radius_pos r) (by norm_num)
  chain := layers_chain _ _ _

theorem physical_dispersion (q : ℝ) (hq : 0<q) (n r : ℕ) :
    ∀ g∈(physicalData q hq n r).gs,g.q^2=g.σ :=
  RadialPairedFamily.layers_parameters _ _ _ (fun qg σg => qg^2=σg) (tm_dispersion q hq n)

theorem physical_parameters (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n r : ℕ) :
    ∀ g∈(physicalData q hq n r).gs,
      1≤g.σ ∧ g.σ≤q^2 ∧ g.q^2≤q^2 ∧ g.q≤q := by
  have hq2 : 1≤q^2 := by nlinarith
  exact RadialPairedFamily.layers_parameters _ _ _
    (fun qg σg => 1≤σg ∧ σg≤q^2 ∧ qg^2≤q^2 ∧ qg≤q)
    (RadialPairedFamily.pairs_parameters q (q^2) hq1 hq2 le_rfl n)

theorem physical_material_bounds (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n r : ℕ) :
    ∀ g∈(physicalData q hq n r).gs,1≤g.σ ∧ g.σ≤q^2 := by
  intro g hg
  have h := physical_parameters q hq hq1 n r g hg
  exact ⟨h.1,h.2.1⟩

theorem physical_te_layers (q : ℝ) (hq : 0<q) (n r : ℕ) :
    (physicalData q hq n r).gs.map SourceDielectricModes.teLayer=
      layers (RadialPairedFamily.te q hq n) (radius r) (radius_pos r) :=
  paired_layers q hq n (radius r) (radius_pos r)

theorem physical_te_outer (q : ℝ) (hq : 0<q) (n r : ℕ) :
    (physicalData q hq n r).X=radius r+width (RadialPairedFamily.te q hq n) := by
  exact congrArg (fun t => radius r+t) (paired_width q hq n)

end OQ14.SourcePairedGeometry

#print axioms OQ14.SourcePairedGeometry.reset_width
#print axioms OQ14.SourcePairedGeometry.reset_layer
#print axioms OQ14.SourcePairedGeometry.reset_layers
#print axioms OQ14.SourcePairedGeometry.reset_pairs
#print axioms OQ14.SourcePairedGeometry.reset_tm
#print axioms OQ14.SourcePairedGeometry.paired_width
#print axioms OQ14.SourcePairedGeometry.paired_layers
#print axioms OQ14.SourcePairedGeometry.tm_dispersion
#print axioms OQ14.SourcePairedGeometry.physical_dispersion
#print axioms OQ14.SourcePairedGeometry.physical_parameters
#print axioms OQ14.SourcePairedGeometry.physical_material_bounds
#print axioms OQ14.SourcePairedGeometry.physical_te_layers
#print axioms OQ14.SourcePairedGeometry.physical_te_outer
