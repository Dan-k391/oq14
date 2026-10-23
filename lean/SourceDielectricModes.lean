import SourceTMPhysicalResponse
import SourceTEPhysicalResponse

/-! One physical dielectric stack supplies every TM and TE angular degree. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceDielectricModes
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.RadialStack

def tmData (d : Data) (l : ℕ) : Data := {d with l := l}

def teLayer (g : Layer) : Layer := {g with σ := 1, σ_pos := zero_lt_one}

theorem te_chain {gs : List Layer} {X R : ℝ} (h : Chain gs X R) :
    Chain (gs.map teLayer) X R := by
  induction h with
  | nil R => exact Chain.nil R
  | cons g gs R h ih => exact Chain.cons (teLayer g) (gs.map teLayer) R ih

def teData (d : Data) (l : ℕ) : Data :=
  {d with l := l, gs := d.gs.map teLayer, chain := te_chain d.chain}

theorem tm_sigma (d : Data) (l : ℕ) (r : ℝ) : sigma (tmData d l) r=sigma d r := rfl

theorem te_sigma (d : Data) (l : ℕ) : ∀ g∈(teData d l).gs,g.σ=1 := by
  intro g hg
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
  rfl

theorem te_select (gs : List Layer) (hdisp : ∀ g∈gs,g.q^2=g.σ) (r : ℝ) :
    ClippedLayerProfiles.select (gs.map teLayer)
      (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0) r=(RadialGluing.sigmaAt gs r : ℂ) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.a<r
    · simp only [List.map_cons,ClippedLayerProfiles.select,teLayer,RadialGluing.sigmaAt,if_pos h,div_one]
      exact congrArg (fun z : ℝ => (z : ℂ)) (hdisp g (by simp))
    · simp only [List.map_cons,ClippedLayerProfiles.select,teLayer,RadialGluing.sigmaAt,if_neg h]
      exact ih (fun a ha => hdisp a (by simp [ha]))

theorem te_mu (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (l : ℕ) (r : ℝ) :
    SourceGeneralMaxwell.mu (teData d l) r=sigma d r := by
  unfold SourceGeneralMaxwell.mu sigma SourceRadialSystem.extend
  change (if r≤d.R then 1 else if r≤d.X then _ else 1)=_
  split_ifs <;> first | rfl | exact te_select d.gs hdisp r

theorem vacuum_inverseSigma (d : Data) (r : ℝ) : inverseSigma (SourceCoreReaction.vacuum d) r=1 := by
  simp only [inverseSigma,SourceRadialSystem.extend,SourceCoreReaction.vacuum]
  split_ifs <;> simp_all

theorem vacuum_raw (d : Data) (r : ℝ) :
    raw (SourceCoreReaction.vacuum d) r=raw (VacuumOutgoingBounds.data d.l) r := by
  rw [SourceCoreReaction.vacuum_raw,VacuumOutgoingHelmholtz.raw_state,
    VacuumOutgoingHelmholtz.u_value,VacuumOutgoingHelmholtz.uD_value]
  rfl

theorem vacuum_electric (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) :
    SourceUnclippedMaxwell.electric (SourceCoreReaction.vacuum d) p x=
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data d.l) p x := by
  ext i
  simp only [SourceUnclippedMaxwell.electric,vacuum_raw,vacuum_inverseSigma,
    VacuumOutgoingHelmholtz.inverse_sigma]
  rfl

theorem vacuum_magnetic (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) :
    SourceUnclippedMaxwell.magnetic (SourceCoreReaction.vacuum d) p x=
      SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data d.l) p x := by
  ext i
  simp only [SourceUnclippedMaxwell.magnetic,vacuum_raw]
  rfl

end OQ14.SourceDielectricModes
#print axioms OQ14.SourceDielectricModes.te_chain
#print axioms OQ14.SourceDielectricModes.tm_sigma
#print axioms OQ14.SourceDielectricModes.te_sigma
#print axioms OQ14.SourceDielectricModes.te_select
#print axioms OQ14.SourceDielectricModes.te_mu
#print axioms OQ14.SourceDielectricModes.vacuum_inverseSigma
#print axioms OQ14.SourceDielectricModes.vacuum_raw
#print axioms OQ14.SourceDielectricModes.vacuum_electric
#print axioms OQ14.SourceDielectricModes.vacuum_magnetic
