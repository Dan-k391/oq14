import SeparatedScatteredRepresentation
import ShellInclusionReaction
import CoreMaterialEvaluation
import FreeDyadicMaterialData
import KernelReciprocity

/-! Identification of the inclusion-weighted shell reaction operator with the bounded material
operator of the literal shell reaction tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ShellReactionIdentification
open MeasureTheory Set Metric OQ14.Maxwell
open scoped ComplexConjugate InnerProductSpace
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-- The sqrt-weighted free dyadic column of the shell at the source point `y` (zero for `‖y‖ ≥ Rin`). -/
def freeDatum (cs : Coefficient) (Rin X : ℝ) (y : Space) (j : Fin 3) : VectorL2 :=
  if hy : ‖y‖ < Rin then
    FreeDyadicMaterialData.datum cs Rin X (fun i => FreeDyadicMaterialData.free Rin X y hy i j)
  else 0

/-- The shell reaction kernel: the dyadic integral of the shell polarization source of the shell
solution with the free datum. -/
def reactionKernel (cs : Coefficient) (R Rin X : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  ∑ h : Fin 3, ∫ z : Space, DynamicVolume.source cs
    (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) (freeDatum cs Rin X y j)) h z *
      DyadicKernel.dyadic 1 (x-z) i h

theorem freeDatum_coordinate (cs : Coefficient) (Rin X : ℝ)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (y : Space) (hy : ‖y‖ < Rin) (i j : Fin 3) :
    (NewtonL2.physicalCoordinate (freeDatum cs Rin X y j) i : Space → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
        DyadicKernel.dyadic 1 (x-y) i j := by
  unfold freeDatum
  rw [dif_pos hy,FreeDyadicMaterialData.datum_coordinate]
  exact WeightedAnnulusDatum.scalarMap_actual cs Rin X _ (fun x => DyadicKernel.dyadic 1 (x-y) i j)
    (fun x => rfl) hcs

theorem inner_phys (h F : VectorL2) :
    ⟪h,F⟫_ℂ = ∑ i : Fin 3, ∫ x : Space,
      ⟪(NewtonL2.physicalCoordinate h i : Space → ℂ) x,(NewtonL2.physicalCoordinate F i : Space → ℂ) x⟫_ℂ := by
  rw [← VectorFourier.components_inner,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪VectorFourier.coordinate i h,VectorFourier.coordinate i F⟫_ℂ = _
  rw [← VectorFourier.scalarCoordinates.inner_map_map (VectorFourier.coordinate i h)
    (VectorFourier.coordinate i F)]
  exact L2.inner_def _ _

theorem inner_scalar (a v : ℂ) : ⟪a,v⟫_ℂ = conj a*v := by
  rw [RCLike.inner_apply]
  ring

theorem scalar_fubini (cs : Coefficient) (Rin X b : ℝ) (hb : b < Rin)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (G : Space → ℂ) (hG : MemLp G 2 volume)
    (s : Space → ℂ) (hs : Integrable s) (hs0 : ∀ y, y ∉ closedBall (0 : Space) b → s y = 0)
    (i j : Fin 3) :
    Integrable (fun x => G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
      ∫ y, DyadicKernel.dyadic 1 (x-y) i j * s y)) ∧
    Integrable (fun y => s y * ∫ x, G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
      DyadicKernel.dyadic 1 (x-y) i j)) ∧
    (∫ x, G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
      ∫ y, DyadicKernel.dyadic 1 (x-y) i j * s y)) =
      ∫ y, s y * ∫ x, G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
        DyadicKernel.dyadic 1 (x-y) i j) := by
  let A := CoreMaterialEvaluation.annulus Rin X
  let B := closedBall (0 : Space) b
  have hAm : MeasurableSet A := (CoreMaterialEvaluation.annulus_compact Rin X).measurableSet
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hAB : IsCompact (A ×ˢ B) := (CoreMaterialEvaluation.annulus_compact Rin X).prod (isCompact_closedBall 0 b)
  let K : Space × Space → ℂ := fun p => G p.1 * ((Real.sqrt (cs.value (VectorFourier.coordinateMap p.1)) : ℂ) *
    DyadicKernel.dyadic 1 (p.1-p.2) i j) * s p.2
  have hne (p : Space × Space) (hp : p ∈ A ×ˢ B) : p.1-p.2≠0 := by
    intro h0
    have h1 := sub_eq_zero.mp h0
    have hn : Rin ≤ ‖p.1‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hp.1.2
    have hn2 : ‖p.2‖ ≤ b := mem_closedBall_zero_iff.mp hp.2
    rw [h1] at hn
    linarith
  have hcont : ContinuousOn (fun p : Space × Space => DyadicKernel.dyadic 1 (p.1-p.2) i j) (A ×ˢ B) := by
    intro p hp
    have hc : ContinuousAt (fun q : Space × Space => q.1-q.2) p := (continuous_fst.sub continuous_snd).continuousAt
    exact (ContinuousAt.comp (g := fun z => DyadicKernel.dyadic 1 z i j) (f := fun q : Space × Space => q.1-q.2)
      (x := p) (ExteriorContinuity.dyadic_continuousAt 1 i j (p.1-p.2) (hne p hp)) hc).continuousWithinAt
  obtain ⟨Kd,hKd⟩ := hAB.exists_bound_of_continuousOn hcont
  have hsq : Measurable (fun x : Space => (Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (cs.measurable.comp VectorFourier.coordinateMap.measurable))
  have hK0x (p : Space × Space) (hp : p.1 ∉ A) : K p = 0 := by
    have : cs.value (VectorFourier.coordinateMap p.1) = 0 := hcs p.1 hp
    simp only [K,this,Real.sqrt_zero,Complex.ofReal_zero,zero_mul,mul_zero]
  have hK0y (p : Space × Space) (hp : p.2 ∉ B) : K p = 0 := by
    simp only [K,hs0 p.2 hp,mul_zero]
  have hGA : Integrable G (volume.restrict A) := by
    haveI : IsFiniteMeasure (volume.restrict A) :=
      isFiniteMeasure_restrict.mpr (CoreMaterialEvaluation.annulus_compact Rin X).measure_ne_top
    exact (hG.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have hsB : Integrable s (volume.restrict B) := hs.restrict
  have hint : Integrable K ((volume.prod volume).restrict (A ×ˢ B)) := by
    rw [← Measure.prod_restrict]
    have hg : Integrable (fun p : Space × Space => (Kd*Real.sqrt cs.bound)*(‖G p.1‖*‖s p.2‖))
        ((volume.restrict A).prod (volume.restrict B)) :=
      (hGA.norm.mul_prod hsB.norm).const_mul _
    rw [Measure.prod_restrict] at hg ⊢
    apply hg.mono'
    · have h1 : AEStronglyMeasurable (fun p : Space × Space => G p.1) (volume.prod volume) :=
        hG.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      have h2 : AEStronglyMeasurable (fun p : Space × Space => s p.2) (volume.prod volume) :=
        hs.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have h3 : AEStronglyMeasurable (fun p : Space × Space =>
          (Real.sqrt (cs.value (VectorFourier.coordinateMap p.1)) : ℂ)) (volume.prod volume) :=
        (hsq.comp measurable_fst).aestronglyMeasurable
      have h4 := hcont.aestronglyMeasurable (hAm.prod hBm) (μ := volume.prod volume)
      exact (h1.restrict.mul (h3.restrict.mul h4)).mul h2.restrict
    · apply ae_restrict_of_forall_mem (hAm.prod hBm)
      intro p hp
      have hsq1 : ‖(Real.sqrt (cs.value (VectorFourier.coordinateMap p.1)) : ℂ)‖ ≤ Real.sqrt cs.bound := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (cs.bounded _)
      have hk := hKd p hp
      change ‖G p.1 * ((Real.sqrt (cs.value (VectorFourier.coordinateMap p.1)) : ℂ) *
        DyadicKernel.dyadic 1 (p.1-p.2) i j) * s p.2‖ ≤ _
      rw [norm_mul,norm_mul,norm_mul]
      have hKd0 : 0 ≤ Kd := (norm_nonneg _).trans hk
      calc
        _ ≤ ‖G p.1‖ * (Real.sqrt cs.bound * Kd) * ‖s p.2‖ := by
          gcongr
        _ = _ := by ring
  have hKi : Integrable K (volume.prod volume) := by
    have hind : (A ×ˢ B).indicator K = K := by
      funext p
      by_cases hp : p ∈ A ×ˢ B
      · rw [indicator_of_mem hp]
      · rw [indicator_of_not_mem hp]
        by_cases h1 : p.1 ∈ A
        · exact (hK0y p (fun h2 => hp ⟨h1,h2⟩)).symm
        · exact (hK0x p h1).symm
    rw [← hind]
    exact (integrable_indicator_iff (hAm.prod hBm)).mpr hint
  have hswap := integral_integral_swap (f := fun x y => K (x,y)) hKi
  have hx (x : Space) : (∫ y, K (x,y)) = G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
      ∫ y, DyadicKernel.dyadic 1 (x-y) i j * s y) := by
    have : (fun y => K (x,y)) = fun y => (G x * (Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ)) *
        (DyadicKernel.dyadic 1 (x-y) i j * s y) := by
      funext y
      simp only [K]
      ring
    rw [this,integral_const_mul]
    ring
  have hy (y : Space) : (∫ x, K (x,y)) = s y * ∫ x, G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
      DyadicKernel.dyadic 1 (x-y) i j) := by
    have : (fun x => K (x,y)) = fun x => s y * (G x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
        DyadicKernel.dyadic 1 (x-y) i j)) := by
      funext x
      simp only [K]
      ring
    rw [this,integral_const_mul]
  refine ⟨?_,?_,?_⟩
  · have := hKi.integral_prod_left
    simpa only [hx] using this
  · have := hKi.integral_prod_right
    simpa only [hy] using this
  · simp only [hx,hy] at hswap
    exact hswap

theorem kernel_core_ae (cs : Coefficient) (Rin X R : ℝ) (hRX : Rin ≤ X) (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, ∀ hx : ‖x‖ < Rin,
      (NewtonL2.physicalCoordinate
        (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier cs v)) i : Space → ℂ) x =
        CoreMaterialEvaluation.evaluation cs Rin X hcs x hx i v := by
  have hcX : ∀ x : Space, x ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap x) = 0 :=
    fun x hx => hcs x (fun h => hx h.1)
  have hρ := fun j => DynamicVolume.source_integrable cs v X hcX j
  have hc := DynamicVolume.source_zero cs v X hcX
  have hcR : ∀ j y, y ∉ closedBall (0 : Space) R → DynamicVolume.source cs v j y = 0 :=
    fun j y hy => hc j y (fun h => hy (closedBall_subset_closedBall hXR h))
  have hF := StaticNewton.material_source_ae cs v
  have hi : ∀ j y, y ∈ ball (0 : Space) Rin → DynamicVolume.source cs v j y = 0 := by
    intro j y hy
    unfold DynamicVolume.source
    rw [hcs y (fun h => h.2 hy)]
    simp
  have h1 := (ae_restrict_iff' measurableSet_closedBall).mp
    (LocalVolumeResponse.electric_ae_on_ball 1 R R (StaticCoefficient.sqrtMultiplier cs v)
      (DynamicVolume.source cs v) hρ hcR hF i)
  have h2 := ConicalInteriorResponse.electric_ae_interior 1 (StaticCoefficient.sqrtMultiplier cs v)
    (DynamicVolume.source cs v) hρ hF Rin X hc hi
  filter_upwards [h1,h2] with x e1 e2 hx
  have hxb : x ∈ ball (0 : Space) Rin := mem_ball_zero_iff.mpr hx
  have hxR : x ∈ closedBall (0 : Space) R := mem_closedBall_zero_iff.mpr (hx.le.trans (hRX.trans hXR))
  rw [SeparatedScatteredRepresentation.kernel_eq_localRepresentative,e1 hxR,
    CoreMaterialEvaluation.evaluation_actual,congrFun (e2 hxb) i]
  unfold ExteriorContinuity.electric KernelConvolution.response
  rfl

theorem weighted_kernel_functional (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (u : VectorL2) (Λ : VectorL2 →L[ℂ] ℂ) :
    Λ (StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci u))) =
      ∑ j : Fin 3, ∫ y : Space, DynamicVolume.source ci u j y * Λ (freeDatum cs Rin X y j) := by
  have hs : ∀ j, Integrable (DynamicVolume.source ci u j) := fun j => DynamicVolume.source_integrable ci u b hci j
  have hs0 : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 :=
    DynamicVolume.source_zero ci u b hci
  have hbX : b ≤ R := (hbR.trans_le (hRX.trans hXR)).le
  obtain ⟨h,hh⟩ : ∃ h : VectorL2, ∀ F, Λ F = ⟪h,F⟫_ℂ :=
    ⟨(InnerProductSpace.toDual ℂ VectorL2).symm Λ,
      fun F => (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm⟩
  let z := ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci u)
  let Gl : Fin 3 → FourierL2.ScalarL2 := fun i =>
    KernelReciprocity.scalarConjugate (NewtonL2.physicalCoordinate h i)
  have hGl (i : Fin 3) : (Gl i : Space → ℂ) =ᵐ[volume]
      fun x => conj ((NewtonL2.physicalCoordinate h i : Space → ℂ) x) :=
    KernelReciprocity.scalarConjugate_ae _
  have hw0 (i : Fin 3) : (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier cs z) i : Space → ℂ)
      =ᵐ[volume] fun x => (Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, DyadicKernel.dyadic 1 (x-y) i j * DynamicVolume.source ci u j y := by
    filter_upwards [NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier cs z) i,
      VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
        (StaticCoefficient.sqrtMultiplier_ae cs z),
      NewtonL2.physicalCoordinate_ae z i,
      SeparatedScatteredRepresentation.kernel_weighted_exterior_ae ci 1 b R hbX u hci i] with x h1 h2 h3 h4
    rw [h1]
    change (StaticCoefficient.sqrtMultiplier cs z) (VectorFourier.coordinateMap x) i = _
    rw [h2]
    by_cases hxa : x ∈ closedBall (0 : Space) X \ ball (0 : Space) Rin
    · have hb1 : b < ‖x‖ := by
        have : Rin ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hxa.2
        linarith
      have hb2 : ‖x‖ ≤ R := (mem_closedBall_zero_iff.mp hxa.1).trans hXR
      change ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) •
        z (VectorFourier.coordinateMap x)) i = _
      rw [Pi.smul_apply,smul_eq_mul,← h3,h4 hb1 hb2]
    · have h0 := hcs x hxa
      change ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) •
        z (VectorFourier.coordinateMap x)) i = _
      simp [h0]
  have hLHS : Λ (StaticCoefficient.sqrtMultiplier cs z) = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space,
      Gl i x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∫ y, DyadicKernel.dyadic 1 (x-y) i j * DynamicVolume.source ci u j y) := by
    rw [hh,inner_phys]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (∫ x : Space, ⟪(NewtonL2.physicalCoordinate h i : Space → ℂ) x,
        (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier cs z) i : Space → ℂ) x⟫_ℂ) =
        ∫ x : Space, Gl i x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
          ∑ j : Fin 3, ∫ y, DyadicKernel.dyadic 1 (x-y) i j * DynamicVolume.source ci u j y) := by
      apply integral_congr_ae
      filter_upwards [hGl i,hw0 i] with x a b'
      rw [inner_scalar,b',a]
    rw [h1]
    simp only [Finset.mul_sum]
    rw [integral_finset_sum]
    intro j _
    exact (scalar_fubini cs Rin X b hbR hcs (Gl i) (Lp.memLp (Gl i)) (DynamicVolume.source ci u j) (hs j)
      (hs0 j) i j).1
  have hpt (j : Fin 3) (y : Space) : DynamicVolume.source ci u j y * Λ (freeDatum cs Rin X y j) =
      ∑ i : Fin 3, DynamicVolume.source ci u j y * ∫ x : Space,
        Gl i x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
          DyadicKernel.dyadic 1 (x-y) i j) := by
    by_cases hy : y ∈ closedBall (0 : Space) b
    · have hyR : ‖y‖ < Rin := (mem_closedBall_zero_iff.mp hy).trans_lt hbR
      rw [hh,inner_phys,← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hGl i,freeDatum_coordinate cs Rin X hcs y hyR i j] with x a c
      rw [inner_scalar,c,a]
    · rw [hs0 j y hy]
      simp
  have hRHS : (∑ j : Fin 3, ∫ y : Space, DynamicVolume.source ci u j y * Λ (freeDatum cs Rin X y j)) =
      ∑ j : Fin 3, ∑ i : Fin 3, ∫ y : Space, DynamicVolume.source ci u j y * ∫ x : Space,
        Gl i x * ((Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) *
          DyadicKernel.dyadic 1 (x-y) i j) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [hpt]
    rw [integral_finset_sum]
    intro i _
    exact (scalar_fubini cs Rin X b hbR hcs (Gl i) (Lp.memLp (Gl i)) (DynamicVolume.source ci u j) (hs j)
      (hs0 j) i j).2.1
  rw [hLHS,hRHS,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact (scalar_fubini cs Rin X b hbR hcs (Gl i) (Lp.memLp (Gl i)) (DynamicVolume.source ci u j) (hs j)
    (hs0 j) i j).2.2

theorem reaction_actual (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X) (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (u : VectorL2) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (ShellInclusionReaction.reaction cs ci 1 R u) i : Space → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (ci.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y : Space, reactionKernel cs R Rin X x y i j * DynamicVolume.source ci u j y := by
  let r := Ring.inverse (DynamicVolume.volumeBlock cs 1 R)
  let w0 := StaticCoefficient.sqrtMultiplier cs
    (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci u))
  have hred : ShellInclusionReaction.reaction cs ci 1 R u =
      StaticCoefficient.sqrtMultiplier ci
        (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier cs (r w0))) := by
    simp only [ShellInclusionReaction.reaction,ShellInclusionReaction.scatteredGreen,
      ContinuousLinearMap.mul_apply]
    rfl
  rw [hred]
  let K := ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier cs (r w0))
  filter_upwards [NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier ci K) i,
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (StaticCoefficient.sqrtMultiplier_ae ci K),
    NewtonL2.physicalCoordinate_ae K i,
    kernel_core_ae cs Rin X R hRX hXR hcs (r w0) i] with x h1 h2 h3 h4
  rw [h1]
  change (StaticCoefficient.sqrtMultiplier ci K) (VectorFourier.coordinateMap x) i = _
  rw [h2]
  change ((Real.sqrt (ci.value (VectorFourier.coordinateMap x)) : ℂ) • K (VectorFourier.coordinateMap x)) i = _
  rw [Pi.smul_apply,smul_eq_mul,← h3]
  by_cases hx : ‖x‖ < Rin
  · rw [h4 hx]
    congr 1
    have hf := weighted_kernel_functional cs ci b Rin X R hbR hRX hXR hcs hci u
      ((CoreMaterialEvaluation.evaluation cs Rin X hcs x hx i).comp r)
    simp only [ContinuousLinearMap.comp_apply] at hf
    rw [hf]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards with y
    rw [CoreMaterialEvaluation.evaluation_actual,mul_comm]
    rfl
  · have hc : ci.value (VectorFourier.coordinateMap x) = 0 := by
      apply hci
      intro hmem
      have := mem_closedBall_zero_iff.mp hmem
      exact hx (this.trans_lt hbR)
    simp [hc]

theorem reactionKernel_eq_evaluation (cs : Coefficient) (R Rin X : ℝ)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (x y : Space) (hx : ‖x‖ < Rin) (i j : Fin 3) :
    reactionKernel cs R Rin X x y i j =
      CoreMaterialEvaluation.evaluation cs Rin X hcs x hx i
        (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) (freeDatum cs Rin X y j)) := by
  rw [CoreMaterialEvaluation.evaluation_actual]
  rfl

end OQ14.ShellReactionIdentification
#print axioms OQ14.ShellReactionIdentification.freeDatum_coordinate
#print axioms OQ14.ShellReactionIdentification.inner_phys
#print axioms OQ14.ShellReactionIdentification.inner_scalar
#print axioms OQ14.ShellReactionIdentification.scalar_fubini
#print axioms OQ14.ShellReactionIdentification.kernel_core_ae
#print axioms OQ14.ShellReactionIdentification.weighted_kernel_functional
#print axioms OQ14.ShellReactionIdentification.reaction_actual
#print axioms OQ14.ShellReactionIdentification.reactionKernel_eq_evaluation
