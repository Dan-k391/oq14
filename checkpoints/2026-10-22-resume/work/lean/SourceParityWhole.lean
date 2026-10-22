import SourceParityFlux

/-! Actual whole-plane free/parity-density coherent bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceParityWhole
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation SourceParityFlux
open SphereReactionKernel (entryBound entryBound_nonnegative)
open scoped Topology

private theorem disk_mass (f : Plane → ℂ) (F : Fin 3 → Plane → ℂ) (T B C m : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (closedBall 0 T))) (hB : 0 ≤ B)
    (hF : ∀ i, IntegrableOn (F i) (closedBall 0 T) ∧ (∫ q : Plane in closedBall 0 T, ‖F i q‖) ≤ C*m)
    (hb : ∀ q, ‖f q‖ ≤ B*(‖F 0 q‖+‖F 1 q‖)) :
    IntegrableOn f (closedBall 0 T) ∧ (∫ q : Plane in closedBall 0 T, ‖f q‖) ≤ 2*B*C*m := by
  have hg := (((hF 0).1.norm.add (hF 1).1.norm).const_mul B)
  have hi := hg.mono' hf (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, B*(‖F 0 q‖+‖F 1 q‖) := integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = B*((∫ q : Plane in closedBall 0 T, ‖F 0 q‖)+(∫ q : Plane in closedBall 0 T, ‖F 1 q‖)) := by
      rw [integral_const_mul,integral_add (hF 0).1.norm (hF 1).1.norm]
    _ ≤ B*(C*m+C*m) := mul_le_mul_of_nonneg_left (add_le_add (hF 0).2 (hF 1).2) hB
    _ = _ := by ring

theorem electric_local (h : Bool) (k R T d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    IntegrableOn (electric h k ρ σ) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖electric h k ρ σ q‖) ≤
      (2*entryBound k*(PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d)))*
        sourceMass ρ*sourceMass σ := by
  have hi := disk_mass (electric h k ρ σ)
    (fun i q => ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i)
    T (entryBound k*sourceMass σ) _ (sourceMass ρ)
    (electric_continuous h k R d hd ρ σ hρ hσ).aestronglyMeasurable.restrict
    (mul_nonneg (entryBound_nonnegative k) (sourceMass_nonnegative σ))
    (fun i => PlaneMaxwellFields.electric_mass k R T d hd ρ hρ i) ?_
  · exact ⟨hi.1,hi.2.trans_eq (by ring)⟩
  · intro q
    change ‖_*star (ParityPlaneFields.magnetic h k σ (MaxwellPlaneTail.planePoint q) 1)-
      _*star (ParityPlaneFields.magnetic h k σ (MaxwellPlaneTail.planePoint q) 0)‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add (mul_le_mul_of_nonneg_left (ParityPlaneFields.magnetic_bound h k σ hσ.integrable _ 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (ParityPlaneFields.magnetic_bound h k σ hσ.integrable _ 0) (norm_nonneg _))).trans_eq (by ring)

theorem magnetic_local (e : Bool) (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    IntegrableOn (magnetic e k ρ σ) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖magnetic e k ρ σ q‖) ≤
      (4*entryBound k*|k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass ρ*sourceMass σ := by
  have hi := disk_mass (magnetic e k ρ σ)
    (fun i q => MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q) i)
    T (entryBound k*sourceMass ρ) _ (sourceMass σ)
    (magnetic_continuous e k R d hd ρ σ hρ hσ).aestronglyMeasurable.restrict
    (mul_nonneg (entryBound_nonnegative k) (sourceMass_nonnegative ρ))
    (fun i => PlaneMaxwellFields.magnetic_mass k R T d hd hdM σ hσ i) ?_
  · exact ⟨hi.1,hi.2.trans_eq (by ring)⟩
  · intro q
    change ‖ParityPlaneFields.electric e k ρ (MaxwellPlaneTail.planePoint q) 0*star _-
      ParityPlaneFields.electric e k ρ (MaxwellPlaneTail.planePoint q) 1*star _‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add (mul_le_mul_of_nonneg_right (ParityPlaneFields.electric_bound e k ρ hρ.integrable _ 0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (ParityPlaneFields.electric_bound e k ρ hρ.integrable _ 1) (norm_nonneg _))).trans_eq (by ring)

private theorem whole_from_parts (f : Plane → ℂ) (T L U m : ℝ)
    (hl : IntegrableOn f (closedBall 0 T) ∧ (∫ q : Plane in closedBall 0 T, ‖f q‖) ≤ L*m)
    (hu : IntegrableOn f {q : Plane | T < ‖q‖} ∧ (∫ q : Plane in {q : Plane | T < ‖q‖}, ‖f q‖) ≤ U*m) :
    Integrable f ∧ (∫ q : Plane, ‖f q‖) ≤ (L+U)*m := by
  have hs : {q : Plane | T < ‖q‖}=(closedBall (0 : Plane) T)ᶜ := by ext q; simp
  rw [hs] at hu
  have hi : Integrable f := by simpa only [union_compl_self,integrableOn_univ] using hl.1.union hu.1
  refine ⟨hi,?_⟩
  rw [← integral_add_compl measurableSet_closedBall hi.norm]
  exact (add_le_add hl.2 hu.2).trans_eq (by ring)

theorem electric_whole (h : Bool) (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    Integrable (electric h k ρ σ) ∧ (∫ q : Plane, ‖electric h k ρ σ q‖) ≤
      SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ*sourceMass σ := by
  have hm : AEStronglyMeasurable (electric h k ρ σ) (volume.restrict {q : Plane | T < ‖q‖}) :=
    (electric_continuous h k R d hd ρ σ hρ hσ).aestronglyMeasurable.restrict
  have hb (q : Plane) (hq : T < ‖q‖) : ‖electric h k ρ σ q‖ ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ*sourceMass σ)/‖q‖^3 :=
    (electric_tail h k R d hR hd hk ρ σ hρ hσ q (by linarith) (by linarith)).trans_eq (by ring)
  have ht := PlaneInverseCube.tail_integrable T _ (by linarith) hm hb
  have htB := PlaneInverseCube.tail_integral_bound T _ (by linarith) hm hb
  have hl := electric_local h k R T d hd ρ σ hρ hσ
  have hh := whole_from_parts _ T
    (2*entryBound k*(PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d)))
    (SourceHerglotzWhole.tailConstant k R T) (sourceMass ρ*sourceMass σ)
    ⟨hl.1,hl.2.trans_eq (by ring)⟩ ⟨ht,htB.trans_eq (by unfold SourceHerglotzWhole.tailConstant; ring)⟩
  exact ⟨hh.1,hh.2.trans_eq (by unfold SourceHerglotzWhole.electricConstant; ring)⟩

theorem magnetic_whole (e : Bool) (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    Integrable (magnetic e k ρ σ) ∧ (∫ q : Plane, ‖magnetic e k ρ σ q‖) ≤
      SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ*sourceMass σ := by
  have hm : AEStronglyMeasurable (magnetic e k ρ σ) (volume.restrict {q : Plane | T < ‖q‖}) :=
    (magnetic_continuous e k R d hd ρ σ hρ hσ).aestronglyMeasurable.restrict
  have hb (q : Plane) (hq : T < ‖q‖) : ‖magnetic e k ρ σ q‖ ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ*sourceMass σ)/‖q‖^3 :=
    (magnetic_tail e k R d hR hd hk ρ σ hρ hσ q (by linarith) (by linarith)).trans_eq (by ring)
  have ht := PlaneInverseCube.tail_integrable T _ (by linarith) hm hb
  have htB := PlaneInverseCube.tail_integral_bound T _ (by linarith) hm hb
  have hl := magnetic_local e k R T d hd hdM ρ σ hρ hσ
  have hh := whole_from_parts _ T
    (4*entryBound k*|k| * PlaneMaxwellSharp.gradientMass k R T d)
    (SourceHerglotzWhole.tailConstant k R T) (sourceMass ρ*sourceMass σ)
    ⟨hl.1,hl.2.trans_eq (by ring)⟩ ⟨ht,htB.trans_eq (by unfold SourceHerglotzWhole.tailConstant; ring)⟩
  exact ⟨hh.1,hh.2.trans_eq (by unfold SourceHerglotzWhole.magneticConstant; ring)⟩

end OQ14.SourceParityWhole
#print axioms OQ14.SourceParityWhole.electric_local
#print axioms OQ14.SourceParityWhole.magnetic_local
#print axioms OQ14.SourceParityWhole.electric_whole
#print axioms OQ14.SourceParityWhole.magnetic_whole
