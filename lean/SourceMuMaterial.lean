import SourceMaterialPartition
import SourceGeneralMaxwell

/-! Literal real permeability coefficient and geometry of the dual radial stack. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceMuMaterial
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.RadialStack

def dualLayer (g : Layer) : Layer :=
  { g with σ := g.q^2/g.σ, σ_pos := div_pos (sq_pos_of_pos g.q_pos) g.σ_pos }

theorem dual_chain {gs : List Layer} {X R : ℝ} (h : Chain gs X R) :
    Chain (gs.map dualLayer) X R := by
  induction h with
  | nil R => exact Chain.nil R
  | cons g gs R h ih => exact Chain.cons (dualLayer g) (gs.map dualLayer) R ih

def dualData (d : Data) : Data := {d with gs := d.gs.map dualLayer, chain := dual_chain d.chain}

theorem sigmaAt_dual (gs : List Layer) (r : ℝ) :
    (RadialGluing.sigmaAt (gs.map dualLayer) r : ℂ)=
      ClippedLayerProfiles.select gs (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0) r := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.a<r
    · simp only [List.map_cons,RadialGluing.sigmaAt,dualLayer,ClippedLayerProfiles.select,if_pos h]
    · simp only [List.map_cons,RadialGluing.sigmaAt,dualLayer,ClippedLayerProfiles.select,if_neg h]
      exact ih

theorem sigma_dual (d : Data) (r : ℝ) : sigma (dualData d) r=SourceGeneralMaxwell.mu d r := by
  unfold sigma SourceGeneralMaxwell.mu SourceRadialSystem.extend
  change (if r≤d.R then 1 else if r≤d.X then _ else 1)=_
  split_ifs <;> first | rfl | exact sigmaAt_dual d.gs r

theorem mu_measurable (d : Data) : Measurable (SourceGeneralMaxwell.mu d) := by
  have h : sigma (dualData d)=SourceGeneralMaxwell.mu d := funext (sigma_dual d)
  rw [←h]
  exact SourceLocalBounds.sigma_measurable (dualData d)

theorem mu_bound (d : Data) : ∃ M : ℝ, 0≤M ∧ ∀ r, ‖SourceGeneralMaxwell.mu d r‖≤M := by
  have h : sigma (dualData d)=SourceGeneralMaxwell.mu d := funext (sigma_dual d)
  rw [←h]
  exact SourceLocalBounds.sigma_bound (dualData d)

theorem dual_parameters (d : Data) (M : ℝ)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) :
    ∀ g∈(dualData d).gs,1≤g.σ ∧ g.σ≤M := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  exact hs a ha

def coefficient (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) : StaticCoefficient.Coefficient :=
  SourceMaterialCoefficient.coefficient (dualData d) M hM (dual_parameters d M hs)

theorem value_complex (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (x : Space) :
    ((coefficient d M hM hs).value (VectorFourier.coordinateMap x) : ℂ)=SourceGeneralMaxwell.mu d ‖x‖-1 := by
  exact (SourceMaterialCoefficient.value_complex (dualData d) M hM (dual_parameters d M hs) x).trans
    (congrArg (fun z : ℂ => z-1) (sigma_dual d ‖x‖))

theorem value_inner (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (x : Space) (hx : ‖x‖≤d.R) :
    (coefficient d M hM hs).value (VectorFourier.coordinateMap x)=0 :=
  SourceMaterialCoefficient.value_inner (dualData d) M hM (dual_parameters d M hs) x hx

theorem value_outer (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (x : Space) (hx : d.X<‖x‖) :
    (coefficient d M hM hs).value (VectorFourier.coordinateMap x)=0 :=
  SourceMaterialCoefficient.value_outer (dualData d) M hM (dual_parameters d M hs) x hx

theorem volumeBlock_isUnit (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (k : ℝ) (hk : 0<k) :
    IsUnit (DynamicVolume.volumeBlock (coefficient d M hM hs) k d.X) :=
  SourceMaterialPartition.volumeBlock_isUnit (dualData d) M hM (dual_parameters d M hs) k hk

end OQ14.SourceMuMaterial
#print axioms OQ14.SourceMuMaterial.dual_chain
#print axioms OQ14.SourceMuMaterial.sigmaAt_dual
#print axioms OQ14.SourceMuMaterial.sigma_dual
#print axioms OQ14.SourceMuMaterial.mu_measurable
#print axioms OQ14.SourceMuMaterial.mu_bound
#print axioms OQ14.SourceMuMaterial.dual_parameters
#print axioms OQ14.SourceMuMaterial.value_complex
#print axioms OQ14.SourceMuMaterial.value_inner
#print axioms OQ14.SourceMuMaterial.value_outer
#print axioms OQ14.SourceMuMaterial.volumeBlock_isUnit
