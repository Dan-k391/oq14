import Packet07DrivenFrameAngularSmooth
import MaxwellFarField

/-! Far-field limits survive proper axial and cyclic rotation of their center. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenRotatedOutgoing
open Filter Maxwell ModalAxialRotation Packet07DrivenAxialPair Packet06CyclicRotation
open scoped Topology

def OutAt (k : ℝ) (c : Space) (F : Field) (A : Space → Vector) : Prop :=
  ∀ v : Space, ‖v‖=1 → Tendsto (fun r : ℝ => MaxwellFarField.factor k r • F (c+r • v)) atTop (𝓝 (A v))

def axialAmplitude (θ : ℝ) (A : Space → Vector) : Space → Vector := fun v => vector θ (A (rotation (-θ) v))
def cyclicAmplitude (A : Space → Vector) : Space → Vector := fun v i => A (unrotate v) (WeakCurl.previous i)

theorem axial_outgoing (θ k : ℝ) (c : Space) (F : Field) (A : Space → Vector) (hF : OutAt k c F A) :
    OutAt k (rotation θ c) (rotateField θ F) (axialAmplitude θ A) := by
  intro v hv
  have hv' : ‖rotation (-θ) v‖=1 := by rw [(rotation (-θ)).norm_map,hv]
  have h := hF (rotation (-θ) v) hv'
  have h0 := (tendsto_pi_nhds.mp h) 0
  have h1 := (tendsto_pi_nhds.mp h) 1
  have h2 := (tendsto_pi_nhds.mp h) 2
  apply tendsto_pi_nhds.mpr
  intro i
  have hx (r : ℝ) : rotation (-θ) (rotation θ c+r • v)=c+r • rotation (-θ) v := by
    rw [map_add,map_smul]
    change spatial (-θ) (spatial θ c)+r • rotation (-θ) v = _
    rw [spatial_inverse]
  fin_cases i
  · have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.cos θ : ℂ)) atTop (𝓝 (Real.cos θ : ℂ))).mul h0).sub ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.sin θ : ℂ)) atTop (𝓝 (Real.sin θ : ℂ))).mul h1)
    apply hh.congr
    intro r
    change (Real.cos θ : ℂ)*(MaxwellFarField.factor k r*F (c+r • rotation (-θ) v) 0) -
      (Real.sin θ : ℂ)*(MaxwellFarField.factor k r*F (c+r • rotation (-θ) v) 1) =
      MaxwellFarField.factor k r*((Real.cos θ : ℂ)*F (rotation (-θ) (rotation θ c+r • v)) 0-
        (Real.sin θ : ℂ)*F (rotation (-θ) (rotation θ c+r • v)) 1)
    rw [hx]
    ring
  · have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.sin θ : ℂ)) atTop (𝓝 (Real.sin θ : ℂ))).mul h0).add ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.cos θ : ℂ)) atTop (𝓝 (Real.cos θ : ℂ))).mul h1)
    apply hh.congr
    intro r
    change (Real.sin θ : ℂ)*(MaxwellFarField.factor k r*F (c+r • rotation (-θ) v) 0) +
      (Real.cos θ : ℂ)*(MaxwellFarField.factor k r*F (c+r • rotation (-θ) v) 1) =
      MaxwellFarField.factor k r*((Real.sin θ : ℂ)*F (rotation (-θ) (rotation θ c+r • v)) 0+
        (Real.cos θ : ℂ)*F (rotation (-θ) (rotation θ c+r • v)) 1)
    rw [hx]
    ring
  · apply h2.congr
    intro r
    simp [rotateField,vector,hx]

theorem cyclic_outgoing (k : ℝ) (c : Space) (F : Field) (A : Space → Vector) (hF : OutAt k c F A) :
    OutAt k (Packet06CyclicRotation.rotation c) (Packet06CyclicRotationMaxwell.rotateField F) (cyclicAmplitude A) := by
  intro v hv
  have hv' : ‖unrotate v‖=1 := by
    change ‖Packet06CyclicRotation.rotation.symm v‖=1
    rw [Packet06CyclicRotation.rotation.symm.norm_map,hv]
  have h := hF (unrotate v) hv'
  apply tendsto_pi_nhds.mpr
  intro i
  have hh := (tendsto_pi_nhds.mp h) (WeakCurl.previous i)
  apply hh.congr
  intro r
  have hx : unrotate (Packet06CyclicRotation.rotation c+r • v)=c+r • unrotate v := by
    change Packet06CyclicRotation.rotation.symm (Packet06CyclicRotation.rotation c+r • v)=_
    rw [map_add,map_smul,Packet06CyclicRotation.rotation.symm_apply_apply]
    rfl
  simp [Packet06CyclicRotationMaxwell.rotateField,cyclicAmplitude,hx]
end OQ14.Packet07DrivenRotatedOutgoing
#print axioms OQ14.Packet07DrivenRotatedOutgoing.axial_outgoing
#print axioms OQ14.Packet07DrivenRotatedOutgoing.cyclic_outgoing
