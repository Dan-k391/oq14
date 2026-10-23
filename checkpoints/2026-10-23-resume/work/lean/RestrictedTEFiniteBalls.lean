import RestrictedTEMaterial
import FiniteBallWeak
import FiniteBallPlaneFields

/-! Actual harmonic TE material solutions and legitimate plane representatives on shrinking finite balls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEFiniteBalls
open MeasureTheory Metric Set MaterialMaxwell SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def solution (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : ℝ → Index →₀ ℂ) (a : ℝ) : VectorFourier.VectorL2 :=
  if ha : 0<a ∧ a≤1 then
    let d := FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha.1 ha.2
    ParityMaterialField.solution d 1 (b/a) (RestrictedTEMaterial.datum _ d (A a))
  else 0

theorem actual_inverse (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ) (hb : b≠0)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : ℝ → Index →₀ ℂ) :
    ∃ η>0, ∀ a : ℝ, 0<a → a<η →
      let c := FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ
      let u := solution p ρ χ R b hρ hχ hi A a
      TestMaxwell 1 (dielectric c) (ParityMaterialField.total c 1 (b/a) u (electric (A a)))
        (ParityMaterialMaxwell.magnetic c 1 (b/a) u (magnetic (A a))) := by
  obtain ⟨η,hη,hs⟩ := FiniteBallWeak.smallness p ρ χ R 1 b hρ hχ hb hi
  refine ⟨η,hη,?_⟩
  intro a ha had
  obtain ⟨ha1,hsmall⟩ := hs a ha had
  have hm := RestrictedTEMaterial.inverse_testMaxwell _
    (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1) (b/a) hsmall (A a)
  simpa only [solution,dif_pos (show 0<a ∧ a≤1 from ⟨ha,ha1⟩)] using hm

theorem source_admissible (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : ℝ → Index →₀ ℂ)
    (ha : 0<a) (ha1 : a≤1) (hh : ∀ l, d+ρ*a≤|p a l 2|) :
    PlaneSourceKernel.Admissible R d
      (DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
        (solution p ρ χ R b hρ hχ hi A a)) :=
  FiniteSpherePlaneSources.material_admissible (p a) (fun _ => ρ*a) χ R d hχ
    (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1) rfl hh _

omit [Fintype ι] in
theorem representative (p : ι → Space) (r : ι → ℝ) (χ R d B : ℝ) (hχ : 0≤χ)
    (hd : 0<d) (hs : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p r χ hχ))
    (hR : hs.radius=R) (hh : ∀ l, d+r l≤|p l 2|) (u : VectorFourier.VectorL2)
    (A : Index →₀ ℂ) (i : Fin 3) :
    let c := FiniteSphereStatic.coefficient p r χ hχ
    let S := DynamicVolume.source c u
    ContinuousOn (fun x => ParityPlaneFields.totalElectric 1 B S (electric A) x i) (NewtonSeparatedResponse.strip d) ∧
    ContinuousOn (fun x => ParityPlaneFields.totalMagnetic 1 B S (magnetic A) x i) (NewtonSeparatedResponse.strip d) ∧
    (∀ᵐ x : Space, x∈NewtonSeparatedResponse.strip d →
      ParityMaterialField.total c 1 B u (electric A) x i=ParityPlaneFields.totalElectric 1 B S (electric A) x i) ∧
    (∀ g : Space → ℂ, ContinuousOn g (NewtonSeparatedResponse.strip d) →
      (∀ᵐ x : Space, x∈NewtonSeparatedResponse.strip d → ParityMaterialField.total c 1 B u (electric A) x i=g x) →
      ∀ z : PlaneInverseCube.Plane, g (MaxwellPlaneTail.planePoint z)=
        ParityPlaneFields.totalElectric 1 B S (electric A) (MaxwellPlaneTail.planePoint z) i) := by
  dsimp only
  have hc (x : Space) (hx : x∉closedBall 0 R) :
      (FiniteSphereStatic.coefficient p r χ hχ).value (VectorFourier.coordinateMap x)=0 := by
    apply hs.ballZero x
    simpa only [hR] using hx
  have hS := DynamicVolume.source_integrable _ u R hc
  have hgap := StaticPlaneInclusions.material_gap p r χ d hχ hh u
  have he := ParityPlaneFields.total_electric_continuousOn 1 B d hd _ hS hgap _
    (fun j => (RestrictedTEMaterial.electric_smooth A j).continuous) i
  have ha := ParityPlaneFields.material_total_ae_strip _ 1 B R d hd u (electric A) hc hgap i
  refine ⟨he,ParityPlaneFields.total_magnetic_continuousOn 1 B d hd _ hS hgap _
    (fun j => (RestrictedTEMaterial.magnetic_smooth A j).continuous) i,ha,?_⟩
  intro g hg hag z
  have heq : ∀ᵐ x : Space, x∈NewtonSeparatedResponse.strip d →
      g x=ParityPlaneFields.totalElectric 1 B (DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u)
        (electric A) x i := by
    filter_upwards [ha,hag] with x hx hy hstrip
    exact (hy hstrip).symm.trans (hx hstrip)
  exact NewtonSeparatedResponse.representative_unique d g _ hg he heq (by
    simp [NewtonSeparatedResponse.strip,MaxwellPlaneTail.planePoint,hd])

end OQ14.RestrictedTEFiniteBalls
#print axioms OQ14.RestrictedTEFiniteBalls.actual_inverse
#print axioms OQ14.RestrictedTEFiniteBalls.source_admissible
#print axioms OQ14.RestrictedTEFiniteBalls.representative
