import SourceMuMaterial
import SourceTECorrection
import SourceExteriorSmooth

/-! Actual compact L2 TE polarization and local bounds for the corrected TE fields. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceMuBounds
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem

theorem polarization_clipped (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) (x : Space) :
    SourceTECorrection.polarization d p i x=(SourceGeneralMaxwell.mu d ‖x‖-1)*
      SourceElectricProfiles.magnetic (SourceCorrectionLocalBounds.clipped d) p x i := by
  by_cases hx : ‖x‖≤d.R
  · simp only [SourceTECorrection.polarization,SourceGeneralMaxwell.mu,
      SourceRadialSystem.extend,if_pos hx,sub_self,zero_mul]
  · have hr : d.R/4<‖x‖ := by linarith [d.hR]
    have he := SourceUnclippedMaxwell.magnetic_agrees d (d.R/4) (by linarith [d.hR]) p x hr
    exact congrArg (fun v : Vector => (SourceGeneralMaxwell.mu d ‖x‖-1)*v i) he.symm

theorem polarization_memLp (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    MemLp (SourceTECorrection.polarization d p i) 2 volume := by
  let g : Space → ℂ := (closedBall 0 d.X).indicator
    (fun x => SourceElectricProfiles.magnetic (SourceCorrectionLocalBounds.clipped d) p x i)
  have hg : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    (SourceLocalBounds.magnetic_memLp_ball (SourceCorrectionLocalBounds.clipped d) p d.X i)
  obtain ⟨M,_,hb⟩ := SourceMuMaterial.mu_bound d
  have hm : Measurable (fun x : Space => SourceGeneralMaxwell.mu d ‖x‖-1) :=
    ((SourceMuMaterial.mu_measurable d).comp continuous_norm.measurable).sub measurable_const
  have hprod : MemLp (fun x => (SourceGeneralMaxwell.mu d ‖x‖-1)*g x) 2 volume := by
    apply hg.of_le_mul (c := M+1) (hm.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with x
    change ‖(SourceGeneralMaxwell.mu d ‖x‖-1)*g x‖≤(M+1)*‖g x‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_right (hb ‖x‖) 1)
  apply hprod.ae_eq
  filter_upwards with x
  by_cases hx : x∈closedBall (0 : Space) d.X
  · simp only [g,Set.indicator_of_mem hx]
    exact (polarization_clipped d p i x).symm
  · simp only [g,Set.indicator_of_not_mem hx,mul_zero]
    exact (SourceTECorrection.polarization_outer d p x
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx) i).symm

theorem polarization_compact (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    HasCompactSupport (SourceTECorrection.polarization d p i) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Space) d.X) isClosed_closedBall
  intro x hx
  exact SourceTECorrection.polarization_outer d p x
    (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx) i

theorem polarization_integrable (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    Integrable (SourceTECorrection.polarization d p i) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) d.X)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 d.X).measure_ne_top
  have hi : IntegrableOn (SourceTECorrection.polarization d p i) (closedBall 0 d.X) :=
    ((polarization_memLp d p i).restrict (closedBall 0 d.X)).integrable (by norm_num : (1 : ENNReal)≤2)
  apply hi.integrable_of_forall_not_mem_eq_zero
  intro x hx
  exact SourceTECorrection.polarization_outer d p x
    (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx) i

theorem electric_memLp_ball (d : Data) (p : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceTECorrection.electric d p x i) 2 (volume.restrict (closedBall 0 T)) :=
  SourceCorrectionLocalBounds.magnetic_memLp_ball d p T i

theorem magnetic_memLp_ball (d : Data) (p : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceTECorrection.magnetic d p x i) 2 (volume.restrict (closedBall 0 T)) :=
  (SourceCorrectionLocalBounds.electric_memLp_ball d p T i).neg

theorem electric_locallyIntegrable (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceTECorrection.electric d p x i) :=
  SourceCorrectionLocalBounds.magnetic_locallyIntegrable d p i

theorem magnetic_locallyIntegrable (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceTECorrection.magnetic d p x i) :=
  (SourceCorrectionLocalBounds.electric_locallyIntegrable d p i).neg

theorem mu_magnetic_memLp_ball (d : Data) (p : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceGeneralMaxwell.mu d ‖x‖*SourceElectricProfiles.magnetic d p x i)
      2 (volume.restrict (closedBall 0 T)) := by
  obtain ⟨M,_,hb⟩ := SourceMuMaterial.mu_bound d
  exact SourceLocalBounds.bounded_mul_memLp_ball _ _
    ((SourceMuMaterial.mu_measurable d).comp continuous_norm.measurable) M (fun x => hb _)
    T (SourceLocalBounds.magnetic_memLp_ball d p T i)

theorem mu_magnetic_locallyIntegrable (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceGeneralMaxwell.mu d ‖x‖*SourceElectricProfiles.magnetic d p x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => mu_magnetic_memLp_ball d p T i)

end OQ14.SourceMuBounds
#print axioms OQ14.SourceMuBounds.polarization_clipped
#print axioms OQ14.SourceMuBounds.polarization_memLp
#print axioms OQ14.SourceMuBounds.polarization_compact
#print axioms OQ14.SourceMuBounds.polarization_integrable
#print axioms OQ14.SourceMuBounds.electric_memLp_ball
#print axioms OQ14.SourceMuBounds.magnetic_memLp_ball
#print axioms OQ14.SourceMuBounds.electric_locallyIntegrable
#print axioms OQ14.SourceMuBounds.magnetic_locallyIntegrable
#print axioms OQ14.SourceMuBounds.mu_magnetic_memLp_ball
#print axioms OQ14.SourceMuBounds.mu_magnetic_locallyIntegrable
