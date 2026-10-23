import RestrictedTEMaterial

/-! Actual scalar scaling and compact first-derivative bounds for finite harmonic TE inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEScale
open Complex MeasureTheory Metric Set Maxwell SymmetricHarmonicJets RestrictedTEIncoming RestrictedTEPlaneLocal
abbrev Space := FourierL2.Space

private def electricMap : (Index →₀ ℂ) →ₗ[ℂ] Field :=
  Finsupp.linearCombination ℂ (fun q x i => ((4*Real.pi : ℂ)*I^q.val.1)*
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i)

private def magneticMap : (Index →₀ ℂ) →ₗ[ℂ] Field :=
  Finsupp.linearCombination ℂ (fun q x i => ((4*Real.pi : ℂ)*I^q.val.1)*
    DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i)

private theorem electricMap_eq (A : Index →₀ ℂ) : electricMap A=electric A := by
  funext x i
  rw [show electric A x i=DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) x i from rfl,electric_sum]
  simp only [electricMap,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [coefficient]
  ring

private theorem magneticMap_eq (A : Index →₀ ℂ) : magneticMap A=magnetic A := by
  funext x i
  rw [show magnetic A x i=DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A) x i from rfl,magnetic_sum]
  simp only [magneticMap,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [coefficient]
  ring

theorem electric_smul (c : ℂ) (A : Index →₀ ℂ) : electric (c • A)=c • electric A := by
  rw [← electricMap_eq,map_smul,electricMap_eq]

theorem magnetic_smul (c : ℂ) (A : Index →₀ ℂ) : magnetic (c • A)=c • magnetic A := by
  rw [← magneticMap_eq,map_smul,magneticMap_eq]

theorem compact_bounds (A : Index →₀ ℂ) (R : ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀ x∈closedBall (0 : Space) R, ∀ i : Fin 3,
      ‖electric A x i‖≤B ∧ ‖fderiv ℝ (fun y => electric A y i) x‖≤B := by
  have hc : Continuous (electric A) := continuous_pi (fun i => (RestrictedTEMaterial.electric_smooth A i).continuous)
  have hd : Continuous (fun x : Space => fun i : Fin 3 => fderiv ℝ (fun y => electric A y i) x) :=
    continuous_pi (fun i => (RestrictedTEMaterial.electric_smooth A i).continuous_fderiv (by simp))
  obtain ⟨U,hU⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨V,hV⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨max 0 (max U V),le_max_left _ _,?_⟩
  intro x hx i
  exact ⟨(norm_le_pi_norm _ i).trans ((hU x hx).trans ((le_max_left U V).trans (le_max_right _ _))),
    (norm_le_pi_norm _ i).trans ((hV x hx).trans ((le_max_right U V).trans (le_max_right _ _)))⟩

theorem scaled_bounds (A : Index →₀ ℂ) (R : ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀ a : ℝ, 0<a → ∀ x∈closedBall (0 : Space) R, ∀ i : Fin 3,
      ‖electric ((a : ℂ)⁻¹ • A) x i‖≤B/a ∧
      ‖fderiv ℝ (fun y => electric ((a : ℂ)⁻¹ • A) y i) x‖≤B/a := by
  obtain ⟨B,hB,hbound⟩ := compact_bounds A R
  refine ⟨B,hB,?_⟩
  intro a ha x hx i
  have hn : ‖(a : ℂ)⁻¹‖=a⁻¹ := by simp [abs_of_pos ha]
  constructor
  · rw [electric_smul,Pi.smul_apply,Pi.smul_apply,norm_smul,hn]
    exact (mul_le_mul_of_nonneg_left (hbound x hx i).1 (inv_nonneg.mpr ha.le)).trans_eq (by ring)
  · have he : (fun y => electric ((a : ℂ)⁻¹ • A) y i)=fun y => (a : ℂ)⁻¹*electric A y i := by
      funext y
      rw [electric_smul]
      rfl
    rw [he,fderiv_const_mul ((RestrictedTEMaterial.electric_smooth A i).contDiffAt.differentiableAt (by simp))]
    apply ((fderiv ℝ (fun y => electric A y i) x).opNorm_smul_le (a : ℂ)⁻¹).trans
    rw [hn]
    exact (mul_le_mul_of_nonneg_left (hbound x hx i).2 (inv_nonneg.mpr ha.le)).trans_eq (by ring)

end OQ14.RestrictedTEScale
#print axioms OQ14.RestrictedTEScale.electric_smul
#print axioms OQ14.RestrictedTEScale.magnetic_smul
#print axioms OQ14.RestrictedTEScale.compact_bounds
#print axioms OQ14.RestrictedTEScale.scaled_bounds
