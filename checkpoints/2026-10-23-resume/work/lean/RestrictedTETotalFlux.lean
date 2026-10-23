import RestrictedTEReactionFlux
import RestrictedTEStaticFlux
import ParityRemainderBound

/-! Literal complete parity total flux and its derived whole-plane harmonic TE remainder budget. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTETotalFlux
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate

def totalFlux (B : ℝ) (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.totalElectric 1 B S (electric A) (MaxwellPlaneTail.planePoint q))
    (conjugate (ParityPlaneFields.totalMagnetic 1 B S (magnetic A) (MaxwellPlaneTail.planePoint q))) 2

def remainder (B : ℝ) (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  conj (((B^2-1 : ℝ) : ℂ))*SourceParityFlux.electric true 1 S S q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*RestrictedTEReactionFlux.flux false S A q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*SourceParityFlux.magnetic false 1 S S q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*conj (((B^2-1 : ℝ) : ℂ))*ParityPlaneBounds.flux false true 1 S S q

theorem total_identity (B : ℝ) (S : Source) (A : Index →₀ ℂ) (q : Plane) :
    totalFlux B S A q=freeFlux S A q+remainder B S A q := by
  have hi (i : Fin 3) (h : i≠2) : electric A (MaxwellPlaneTail.planePoint q) i=0 := electric_tangent_zero A q i h
  have he (i : Fin 3) (h : i≠2) : ParityPlaneFields.electric true 1 S (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityPlaneFields.electric_true_zero 1 S _ (by rfl) i h
  have hh (i : Fin 3) (h : i≠2) : ParityPlaneFields.magnetic false 1 S (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityPlaneFields.magnetic_false_zero 1 S _ (by rfl) i h
  unfold totalFlux ParityPlaneFields.totalElectric ParityPlaneFields.totalMagnetic freeFlux remainder
    SourceParityFlux.electric SourceParityFlux.magnetic ParityPlaneBounds.flux RestrictedTEReactionFlux.flux
  simp [cross_apply,conjugate]
  rw [hi 0 (by decide),hi 1 (by decide),he 0 (by decide),he 1 (by decide),hh 0 (by decide),hh 1 (by decide)]
  simp only [mul_zero,zero_add,add_zero,map_add,map_mul,map_zero,Complex.star_def]
  ring

private theorem add_mass (f g : Plane → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ q : Plane, ‖f q+g q‖)≤(∫ q : Plane, ‖f q‖)+(∫ q : Plane, ‖g q‖) := by
  rw [← integral_add hf.norm hg.norm]
  exact integral_mono_ae (hf.add hg).norm (hf.norm.add hg.norm)
    (Filter.Eventually.of_forall (fun q => norm_add_le _ _))

private theorem scaled_mass (z : ℂ) (f : Plane → ℂ) (C : ℝ) (hf : (∫ q : Plane, ‖f q‖)≤C) :
    (∫ q : Plane, ‖z*f q‖)≤‖z‖*C := by
  simp only [norm_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_left hf (norm_nonneg z)

theorem whole_bounds (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ Ci Cp : ℝ, 0≤Ci ∧ 0≤Cp ∧ ∀ (B T d : ℝ), 0<d → 2≤T → 2*R≤T → d≤T+R →
      ∀ (S : Source), Admissible R d S → ∀ c : ℂ,
        Integrable (remainder B S (c • A)) ∧ Integrable (totalFlux B S (c • A)) ∧
          (∫ q : Plane, ‖remainder B S (c • A) q‖)≤
            ParityRemainderBound.budget 1 B R T d Ci Cp (sourceMass S) ‖c‖ := by
  obtain ⟨Ci,hCi,hinc⟩ := RestrictedTEReactionFlux.whole_scaled_bound A R hR
  obtain ⟨Cp,hCp,hpar⟩ := ParityPlaneBounds.whole_bound 1 R hR one_ne_zero
  refine ⟨Ci,Cp,hCi,hCp,?_⟩
  intro B T d hd hT hTR hdM S hS c
  have he := SourceParityWhole.electric_whole true 1 R T d hR hd one_ne_zero hT hTR S S hS hS
  have hi := hinc false d S hS c
  have hm := SourceParityWhole.magnetic_whole false 1 R T d hR hd one_ne_zero hT hTR hdM S S hS hS
  have hr := hpar false true d S S hS hS
  let ze : ℂ := ((B^2-1 : ℝ) : ℂ)
  let zm : ℂ := ((B⁻¹^2-1 : ℝ) : ℂ)
  let f1 : Plane → ℂ := fun q => conj ze*SourceParityFlux.electric true 1 S S q
  let f2 : Plane → ℂ := fun q => zm*RestrictedTEReactionFlux.flux false S (c • A) q
  let f3 : Plane → ℂ := fun q => zm*SourceParityFlux.magnetic false 1 S S q
  let f4 : Plane → ℂ := fun q => (zm*conj ze)*ParityPlaneBounds.flux false true 1 S S q
  have hf1 : Integrable f1 := he.1.const_mul _
  have hf2 : Integrable f2 := hi.1.const_mul _
  have hf3 : Integrable f3 := hm.1.const_mul _
  have hf4 : Integrable f4 := hr.1.const_mul _
  have hrem : Integrable (remainder B S (c • A)) := ((hf1.add hf2).add hf3).add hf4
  have hbase := RestrictedTEStaticFlux.dynamic_integrable (c • A) R d hR hd S hS
  obtain ⟨_,_,hqq⟩ := MaxwellPlaneL1.whole_plane_bound 1 R d hR hd
  have hfree : Integrable (freeFlux S (c • A)) := (hbase.add (hqq S S hS hS).1).congr
    (Filter.Eventually.of_forall (fun q => (free_identity S (c • A) q).symm))
  have htotal : Integrable (totalFlux B S (c • A)) := (hfree.add hrem).congr
    (Filter.Eventually.of_forall (fun q => (total_identity B S (c • A) q).symm))
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
    _ ≤ ((‖conj ze‖*(SourceHerglotzWhole.electricConstant 1 R T d*sourceMass S*sourceMass S)+
        ‖zm‖*(Ci*sourceMass S*‖c‖))+‖zm‖*(SourceHerglotzWhole.magneticConstant 1 R T d*sourceMass S*sourceMass S))+
        ‖zm*conj ze‖*(Cp*sourceMass S*sourceMass S) := add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4
    _ = _ := by
      dsimp [ze,zm]
      simp only [norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs]
      unfold ParityRemainderBound.budget
      ring

end OQ14.RestrictedTETotalFlux
#print axioms OQ14.RestrictedTETotalFlux.total_identity
#print axioms OQ14.RestrictedTETotalFlux.whole_bounds
