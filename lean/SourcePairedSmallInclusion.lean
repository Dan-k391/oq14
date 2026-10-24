import SourcePairedSmallness

/-! Smallness of the limiting effective block is automatic for small inclusions: the limit kernel norm
has an explicit bound independent of the radius, the dynamic error bound is quadratic in the radius, and
the carrier volume is cubic. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace OQ14.SourcePairedSmallInclusion
open Filter Topology Metric MeasureTheory OQ14.ShellInclusionVolume OQ14.ShellInclusionReaction
  OQ14.SourcePairedInclusion OQ14.SourcePairedReduction OQ14.SourcePairedSmallness
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev Space := FourierL2.Space

theorem even_bound (x y : Space) (i j : Fin 3) :
    ‖OQ14.CentralReactionExpansion.evenKernel x y i j‖ ≤ SphereReactionKernel.entryBound 1 := by
  unfold OQ14.CentralReactionExpansion.evenKernel
  rw [norm_div]
  have h := (norm_add_le (SphereReactionKernel.J 1 (x-y) i j) (SphereReactionKernel.J 1 (x-(-y)) i j)).trans
    (add_le_add (SphereReactionKernel.J_bound 1 _ i j) (SphereReactionKernel.J_bound 1 _ i j))
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2,div_le_iff₀ (by norm_num)]
  linarith

theorem odd_bound (x y : Space) (i j : Fin 3) :
    ‖OQ14.CentralReactionExpansion.oddKernel x y i j‖ ≤ SphereReactionKernel.entryBound 1 := by
  unfold OQ14.CentralReactionExpansion.oddKernel
  rw [norm_div]
  have h := (norm_sub_le (SphereReactionKernel.J 1 (x-y) i j) (SphereReactionKernel.J 1 (x-(-y)) i j)).trans
    (add_le_add (SphereReactionKernel.J_bound 1 _ i j) (SphereReactionKernel.J_bound 1 _ i j))
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2,div_le_iff₀ (by norm_num)]
  linarith

/-- Explicit radius-independent bound of the limit kernel norm. -/
def kernelConstant (q : ℝ) (n : ℕ) : ℝ :=
  9*(|q^(2*n)-1|+|(q^(2*n))⁻¹-1|)*SphereReactionKernel.entryBound 1

theorem limitKernelNorm_le (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) :
    limitKernelNorm q hq n b ≤ kernelConstant q n := by
  have hE := SphereReactionKernel.entryBound_nonnegative 1
  have hentry (i j : Fin 3) : ‖SourcePairedCore.limitMap q hq n b i j‖ ≤
      (|q^(2*n)-1|+|(q^(2*n))⁻¹-1|)*SphereReactionKernel.entryBound 1 := by
    rw [ContinuousMap.norm_le _ (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hE)]
    intro p
    rw [SourcePairedCore.limitMap_apply q hq n b hb.le i j p]
    unfold VectorLimitIdentification.kernel
    have hA : ‖(((q^(2*n) : ℝ) : ℂ)-1)‖ = |q^(2*n)-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hB : ‖((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)‖ = |(q^(2*n))⁻¹-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [norm_mul,Complex.norm_I,one_mul]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,hA,hB]
    calc _ ≤ |q^(2*n)-1| * SphereReactionKernel.entryBound 1+|(q^(2*n))⁻¹-1| * SphereReactionKernel.entryBound 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (even_bound _ _ i j) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (odd_bound _ _ i j) (abs_nonneg _))
      _ = _ := by ring
  unfold limitKernelNorm kernelConstant
  calc _ ≤ ∑ _i : Fin 3,∑ _j : Fin 3,(|q^(2*n)-1|+|(q^(2*n))⁻¹-1|)*SphereReactionKernel.entryBound 1 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; ring

theorem entryMass_one (b : ℝ) :
    DynamicConvolution.entryMass 1 (2*b) =
      ((14/(4*Real.pi))*((3/2 : ℝ)*(volume : MeasureTheory.Measure Space).real (ball 0 1)*4))*b^2 := by
  unfold DynamicConvolution.entryMass
  ring

theorem errorBound_tendsto (ci : Coefficient) :
    Tendsto (fun b : ℝ => DynamicVolume.errorBound ci 1 b) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun b : ℝ => DynamicVolume.errorBound ci 1 b) := by
    unfold DynamicVolume.errorBound DynamicConvolution.entryMass
    fun_prop
  have h0 : DynamicVolume.errorBound ci 1 0 = 0 := by
    unfold DynamicVolume.errorBound DynamicConvolution.entryMass
    simp
  exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa only [h0] using hc.tendsto 0)

theorem carrier_volume_le (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 ≤ b)
    (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b) :
    volume.real d.carrier ≤ b^3*(volume : MeasureTheory.Measure Space).real (ball 0 1) := by
  have hs : d.carrier ⊆ closedBall (0 : Space) b := fun x hx => mem_closedBall_zero_iff.mpr (hcar x hx)
  have h := Measure.addHaar_real_closedBall (volume : MeasureTheory.Measure Space) (0 : Space) hb
  rw [finrank_euclideanSpace_fin] at h
  rw [← h]
  exact measureReal_mono hs (measure_closedBall_lt_top).ne

theorem exists_small_radius (q : ℝ) (hq : 1≤q) (n : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃ b0 : ℝ, 0<b0 ∧ ∀ b : ℝ, 0<b → b ≤ b0 → ∀ (ci : Coefficient), ci.bound ≤ M →
      ∀ d : BoundedMaterialKernel.SupportData ci, (∀ x ∈ d.carrier,‖x‖ ≤ b) →
        dataSmallness q hq n ci d b<1 := by
  set V := (volume : MeasureTheory.Measure Space).real (ball 0 1) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set C := kernelConstant q n with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    unfold kernelConstant
    have := SphereReactionKernel.entryBound_nonnegative 1
    positivity
  set c0 := (14/(4*Real.pi))*((3/2 : ℝ)*V*4) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set K := 9*c0*M+M*V*C with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min 1 (1/(2*(K+1))),lt_min one_pos (by positivity),?_⟩
  intro b hb hbb ci hci d hcar
  have hb1 : b ≤ 1 := hbb.trans (min_le_left _ _)
  have hb2 : b ≤ 1/(2*(K+1)) := hbb.trans (min_le_right _ _)
  have hen : DynamicVolume.errorBound ci 1 b ≤ 9*c0*M*b := by
    unfold DynamicVolume.errorBound
    rw [entryMass_one]
    have : b^2 ≤ b := by nlinarith
    have hmb : 0 ≤ 9*c0 := by positivity
    calc 9*(c0*b^2)*ci.bound ≤ 9*(c0*b)*M := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hc00) (by norm_num))
            hci (le_trans (c := ci.bound) (by exact ci.nonnegative 0 |>.trans (ci.bounded 0)) le_rfl) (by positivity)
      _ = 9*c0*M*b := by ring
  have hvol := carrier_volume_le ci d b hb.le hcar
  have hker := limitKernelNorm_le q hq n b hb
  have hcb0 : 0 ≤ ci.bound := (ci.nonnegative 0).trans (ci.bounded 0)
  have hvr : 0 ≤ volume.real d.carrier := measureReal_nonneg
  have hl0 : 0 ≤ limitKernelNorm q hq n b := by
    unfold limitKernelNorm
    positivity
  have hsec : ci.bound*volume.real d.carrier*limitKernelNorm q hq n b ≤ M*V*C*b := by
    have h3 : b^3 ≤ b := by nlinarith [sq_nonneg b]
    calc ci.bound*volume.real d.carrier*limitKernelNorm q hq n b
        ≤ M*(b^3*V)*C := by
          apply mul_le_mul (mul_le_mul hci hvol hvr hM) hker hl0 (by positivity)
      _ ≤ M*(b*V)*C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul_of_nonneg_left _ hM
          exact mul_le_mul_of_nonneg_right h3 hV0
      _ = _ := by ring
  unfold dataSmallness
  have hfin : (9*c0*M+M*V*C)*b < 1 := by
    have hKb : K*b ≤ K*(1/(2*(K+1))) := mul_le_mul_of_nonneg_left hb2 hK0
    have : K*(1/(2*(K+1))) < 1 := by
      rw [mul_one_div,div_lt_one (by positivity)]
      linarith
    exact lt_of_le_of_lt hKb this
  calc _ ≤ 9*c0*M*b+M*V*C*b := add_le_add hen hsec
    _ = (9*c0*M+M*V*C)*b := by ring
    _ < 1 := hfin

theorem eventually_combined_isUnit_small (q : ℝ) (hq : 1≤q) (n : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃ b0 : ℝ, 0<b0 ∧ ∀ b : ℝ, 0<b → b ≤ b0 → ∀ (ci : Coefficient), ci.bound ≤ M →
      ∀ d : BoundedMaterialKernel.SupportData ci, (∀ x ∈ d.carrier,‖x‖ ≤ b) →
        ∀ᶠ r : ℕ in atTop,IsUnit (DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X) := by
  obtain ⟨b0,hb0,h⟩ := exists_small_radius q hq n M hM
  refine ⟨b0,hb0,?_⟩
  intro b hb hbb ci hci d hcar
  exact eventually_combined_isUnit_of_data q hq n ci d b hb hcar (h b hb hbb ci hci d hcar)

end OQ14.SourcePairedSmallInclusion
#print axioms OQ14.SourcePairedSmallInclusion.even_bound
#print axioms OQ14.SourcePairedSmallInclusion.odd_bound
#print axioms OQ14.SourcePairedSmallInclusion.limitKernelNorm_le
#print axioms OQ14.SourcePairedSmallInclusion.entryMass_one
#print axioms OQ14.SourcePairedSmallInclusion.errorBound_tendsto
#print axioms OQ14.SourcePairedSmallInclusion.carrier_volume_le
#print axioms OQ14.SourcePairedSmallInclusion.exists_small_radius
#print axioms OQ14.SourcePairedSmallInclusion.eventually_combined_isUnit_small
