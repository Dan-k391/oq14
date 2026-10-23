import ParityTotalFlux
import SourceParityWhole

/-! Derived whole-plane remainder bounds for the complete electric-wall parity material plane field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityRemainderBound
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation ParityTotalFlux
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def budget (k B R T d Ci Cp m w : ℝ) : ℝ :=
  |B^2-1| *SourceHerglotzWhole.electricConstant k R T d*m^2+
    |B⁻¹^2-1| *Ci*m*w+
    |B⁻¹^2-1| *SourceHerglotzWhole.magneticConstant k R T d*m^2+
    |B⁻¹^2-1| *|B^2-1| *Cp*m^2

private theorem add_mass (f g : Plane → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ q : Plane, ‖f q+g q‖) ≤ (∫ q : Plane, ‖f q‖)+(∫ q : Plane, ‖g q‖) := by
  rw [← integral_add hf.norm hg.norm]
  exact integral_mono_ae (hf.add hg).norm (hf.norm.add hg.norm)
    (Filter.Eventually.of_forall (fun q => norm_add_le _ _))

private theorem scaled_mass (z : ℂ) (f : Plane → ℂ) (C : ℝ) (hf : (∫ q : Plane, ‖f q‖) ≤ C) :
    (∫ q : Plane, ‖z*f q‖) ≤ ‖z‖*C := by
  simp only [norm_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_left hf (norm_nonneg z)

theorem whole_bounds (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ Ci Cp : ℝ, 0 ≤ Ci ∧ 0 ≤ Cp ∧ ∀ (B T d : ℝ), 0 < d → 2 ≤ T → 2*R ≤ T → d ≤ T+R →
      ∀ (ρ : Source), Admissible R d ρ → ∀ (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ),
      (∀ s, p s ∈ closedBall 0 R) →
      Integrable (remainder k B ρ p j A) ∧ Integrable (totalFlux k B ρ p j A) ∧
        (∫ q : Plane, ‖remainder k B ρ p j A q‖) ≤ budget k B R T d Ci Cp (sourceMass ρ) (∑ s, ‖A s‖) := by
  obtain ⟨Ci,hCi,hinc⟩ := ParityIncidentFlux.whole_bound (ι := ι) k R hR hk
  obtain ⟨Cp,hCp,hpar⟩ := ParityPlaneBounds.whole_bound k R hR hk
  refine ⟨Ci,Cp,hCi,hCp,?_⟩
  intro B T d hd hT hTR hdM ρ hρ p j A hp
  have he := SourceParityWhole.electric_whole true k R T d hR hd hk hT hTR ρ ρ hρ hρ
  have hi := hinc false d ρ hρ (fun _ => true) p j A hp
  have hm := SourceParityWhole.magnetic_whole false k R T d hR hd hk hT hTR hdM ρ ρ hρ hρ
  have hr := hpar false true d ρ ρ hρ hρ
  let ze : ℂ := ((B^2-1 : ℝ) : ℂ)
  let zm : ℂ := ((B⁻¹^2-1 : ℝ) : ℂ)
  let f1 : Plane → ℂ := fun q => conj ze*SourceParityFlux.electric true k ρ ρ q
  let f2 : Plane → ℂ := fun q => zm*ParityIncidentFlux.flux false k ρ (fun _ => true) p j A q
  let f3 : Plane → ℂ := fun q => zm*SourceParityFlux.magnetic false k ρ ρ q
  let f4 : Plane → ℂ := fun q => (zm*conj ze)*ParityPlaneBounds.flux false true k ρ ρ q
  have hf1 : Integrable f1 := he.1.const_mul _
  have hf2 : Integrable f2 := hi.1.const_mul _
  have hf3 : Integrable f3 := hm.1.const_mul _
  have hf4 : Integrable f4 := hr.1.const_mul _
  have hrem : Integrable (remainder k B ρ p j A) := (hf1.add hf2 |>.add hf3 |>.add hf4)
  have hbase := SourceHerglotzFinite.electric_mass k R T d hR hd hk hT hTR ρ hρ (fun _ => true) p j A hp
  obtain ⟨_,_,hqq⟩ := MaxwellPlaneL1.whole_plane_bound k R d hR hd
  have hfree : Integrable (freeFlux k ρ p j A) := (hbase.1.add (hqq ρ ρ hρ hρ).1).congr
    (Filter.Eventually.of_forall (fun q => (free_identity k ρ p j A q).symm))
  have htotal : Integrable (totalFlux k B ρ p j A) := (hfree.add hrem).congr
    (Filter.Eventually.of_forall (fun q => (total_identity k B ρ p j A q).symm))
  refine ⟨hrem,htotal,?_⟩
  have hb1 := scaled_mass (conj ze) _ _ he.2
  have hb2 := scaled_mass zm _ _ hi.2
  have hb3 := scaled_mass zm _ _ hm.2
  have hb4 := scaled_mass (zm*conj ze) _ _ hr.2
  calc
    _ ≤ ((∫ q : Plane, ‖f1 q‖)+(∫ q : Plane, ‖f2 q‖))+(∫ q : Plane, ‖f3 q‖)+(∫ q : Plane, ‖f4 q‖) :=
      (add_mass _ f4 ((hf1.add hf2).add hf3) hf4).trans
        (add_le_add_right ((add_mass _ f3 (hf1.add hf2) hf3).trans
          (add_le_add_right (add_mass f1 f2 hf1 hf2) _)) _)
    _ ≤ ((‖conj ze‖*(SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ*sourceMass ρ)+
      ‖zm‖*(Ci*sourceMass ρ*(∑ s, ‖A s‖)))+
      ‖zm‖*(SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ*sourceMass ρ))+
      ‖zm*conj ze‖*(Cp*sourceMass ρ*sourceMass ρ) := add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4
    _ = _ := by
      dsimp [ze,zm]
      simp only [norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs]
      unfold budget
      ring

end OQ14.ParityRemainderBound
#print axioms OQ14.ParityRemainderBound.whole_bounds
