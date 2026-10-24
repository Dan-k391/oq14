import SourcePairedWallKernelAE
import ParityPlaneFields

/-! The shell-reaction field at arbitrary points, its uniform convergence on compact sets to the limit
field of the central-inversion kernel, and the identification of that limit with the parity plane reaction
fields (exactly on half-turn invariant sources). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourcePairedReactionField
open MeasureTheory Set Metric Filter OQ14.Maxwell
open PhysicalReactionLimit (Region)
open scoped Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-- The shell-reaction field of the literal shell reaction kernel at an arbitrary point. -/
def reactionField (cs ci : Coefficient) (R Rin X : ℝ) (u : VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y : Space, ShellReactionIdentification.reactionKernel cs R Rin X x y i j *
    DynamicVolume.source ci u j y

/-- The field of the limiting central-inversion kernel. -/
def limitField (q : ℝ) (n : ℕ) (ci : Coefficient) (u : VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y : Space, VectorLimitIdentification.kernel q n i j (x,y) * DynamicVolume.source ci u j y

theorem reaction_eq_sqrt_reactionField (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (u : VectorL2) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (ShellInclusionReaction.reaction cs ci 1 R u) i : Space → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (ci.value (VectorFourier.coordinateMap x)) : ℂ) * reactionField cs ci R Rin X u x i :=
  ShellReactionIdentification.reaction_actual cs ci b Rin X R hbR hRX hXR hcs hci u i

/-! ### Uniform convergence of the kernels on compact sets -/

theorem paired_kernel_tendsto_uniform_compact (q : ℝ) (hq : 1≤q) (n : ℕ) (ρ0 b : ℝ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x y : Space, ‖x‖ ≤ ρ0 → ‖y‖ ≤ b → ∀ i j : Fin 3,
      ‖SourcePairedTensor.kernel q hq n r i j (x,y)-VectorLimitIdentification.kernel q n i j (x,y)‖ ≤ ε := by
  let b' : ℝ := max (max ρ0 b) 1
  have hb' : 0<b' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hall (i j : Fin 3) : ∀ᶠ r : ℕ in atTop, ∀ p : Region b',
      ‖SourcePairedTensor.kernel q hq n r i j p.val-VectorLimitIdentification.kernel q n i j p.val‖ ≤ ε := by
    have hlim := (tendsto_iff_norm_sub_tendsto_zero.mp (SourcePairedCore.actualMap_limit q hq n b' hb'.le i j)).eventually
      (gt_mem_nhds hε)
    filter_upwards [SourcePairedCore.eventually_actualMap q hq n b' hb'.le i j,hlim] with r h1 h2
    intro p
    have h3 : ‖(SourcePairedCore.actualMap q hq n b' i j r-SourcePairedCore.limitMap q hq n b' i j) p‖ ≤
        ‖SourcePairedCore.actualMap q hq n b' i j r-SourcePairedCore.limitMap q hq n b' i j‖ :=
      ContinuousMap.norm_coe_le_norm _ p
    rw [ContinuousMap.sub_apply,h1 p,SourcePairedCore.limitMap_apply q hq n b' hb'.le i j p] at h3
    exact h3.trans h2.le
  have hall' : ∀ᶠ r : ℕ in atTop, ∀ i j : Fin 3, ∀ p : Region b',
      ‖SourcePairedTensor.kernel q hq n r i j p.val-VectorLimitIdentification.kernel q n i j p.val‖ ≤ ε :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => hall i j))
  filter_upwards [hall'] with r hr
  intro x y hx hy i j
  exact hr i j ⟨(x,y),SourceCoreOperator.pair_mem_region b' x y
    (hx.trans ((le_max_left _ _).trans (le_max_left _ _)))
    (hy.trans ((le_max_right _ _).trans (le_max_left _ _)))⟩

/-! ### Source masses -/

theorem source_mass' (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (v : VectorL2) (j : Fin 3) :
    (∫ y : Space, ‖DynamicVolume.source ci v j y‖) ≤
      (Real.sqrt ci.bound*Real.sqrt (volume.real d.carrier))*‖v‖ := by
  have h := BoundedMaterialKernel.source_mass d v j
  have he : (∫ y : Space, ‖DynamicVolume.source ci v j y‖)=
      ∫ y : Space, ‖DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier ci v) y‖ := by
    apply integral_congr_ae
    filter_upwards [StaticNewton.material_source_ae ci v j] with y hy
    rw [DynamicConvolution.component_apply,hy]
    rfl
  rw [he]
  calc _ ≤ _ := h
    _ = _ := by ring

theorem source_sub_ae (ci : Coefficient) (u v : VectorL2) (j : Fin 3) :
    DynamicVolume.source ci (u-v) j =ᵐ[volume]
      fun y => DynamicVolume.source ci u j y-DynamicVolume.source ci v j y := by
  filter_upwards [VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_sub u v)] with y hy
  have hsub : ∀ a b : Vector, (a-b) j=a j-b j := fun a b => rfl
  simp only [DynamicVolume.source]
  rw [hy]
  simp only [Pi.sub_apply]
  rw [hsub]
  ring

theorem norm_integral_mul_le (k s : Space → ℂ) (C : ℝ) (hk : ∀ y, ‖k y‖ ≤ C)
    (hkm : AEStronglyMeasurable k volume) (hs : Integrable s) :
    ‖∫ y : Space, k y*s y‖ ≤ C*∫ y : Space, ‖s y‖ := by
  have hi : Integrable (fun y => k y*s y) := hs.bdd_mul' hkm (Eventually.of_forall hk)
  calc ‖∫ y : Space, k y*s y‖ ≤ ∫ y : Space, ‖k y*s y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Space, C*‖s y‖ := by
      apply integral_mono hi.norm (hs.norm.const_mul C)
      intro y
      show ‖k y*s y‖ ≤ C*‖s y‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hk y) (norm_nonneg _)
    _ = C*∫ y : Space, ‖s y‖ := integral_const_mul _ _

/-! ### The field convergence -/

theorem kernel_continuous_slice (A : BoundedMaterialKernel.Kernel) (x : Space) :
    Continuous (fun y => A.value x y) :=
  A.continuous.comp (continuous_const.prodMk continuous_id)

theorem split_bound (A L : BoundedMaterialKernel.Kernel) (δ F : ℝ)
    (hδ : ∀ x y, ‖A.value x y-L.value x y‖ ≤ δ) (hF : ∀ x y, ‖L.value x y‖ ≤ F)
    (s1 s2 : Space → ℂ) (h1 : Integrable s1) (h2 : Integrable s2) (x : Space) :
    ‖(∫ y : Space, A.value x y*s1 y)-∫ y : Space, L.value x y*s2 y‖ ≤
      δ*(∫ y : Space, ‖s1 y‖)+F*∫ y : Space, ‖s1 y-s2 y‖ := by
  have hAc := kernel_continuous_slice A x
  have hLc := kernel_continuous_slice L x
  have hI1 : Integrable (fun y => A.value x y*s1 y) :=
    h1.bdd_mul' hAc.aestronglyMeasurable (Eventually.of_forall (fun y => A.bounded x y))
  have hI2 : Integrable (fun y => L.value x y*s2 y) :=
    h2.bdd_mul' hLc.aestronglyMeasurable (Eventually.of_forall (fun y => L.bounded x y))
  have hk1 : Integrable (fun y => (A.value x y-L.value x y)*s1 y) :=
    h1.bdd_mul' (hAc.sub hLc).aestronglyMeasurable (Eventually.of_forall (fun y => hδ x y))
  have hk2 : Integrable (fun y => L.value x y*(s1 y-s2 y)) :=
    (h1.sub h2).bdd_mul' hLc.aestronglyMeasurable (Eventually.of_forall (fun y => L.bounded x y))
  have hsplit : (∫ y : Space, A.value x y*s1 y)-(∫ y : Space, L.value x y*s2 y)=
      (∫ y : Space, (A.value x y-L.value x y)*s1 y)+∫ y : Space, L.value x y*(s1 y-s2 y) := by
    rw [← integral_add hk1 hk2,← integral_sub hI1 hI2]
    congr 1
    funext y
    ring
  rw [hsplit]
  have b1 := norm_integral_mul_le (fun y => A.value x y-L.value x y) s1 δ (fun y => hδ x y)
    (hAc.sub hLc).aestronglyMeasurable h1
  have b2 := norm_integral_mul_le (fun y => L.value x y) (fun y => s1 y-s2 y) F (fun y => hF x y)
    hLc.aestronglyMeasurable (h1.sub h2)
  exact (norm_add_le _ _).trans (add_le_add b1 b2)

theorem extension_diff_le (b : ℝ) (hb : 0<b) (f g : C(Region b,ℂ)) (x y : Space) :
    ‖(CompactCoreKernel.extension b hb f).value x y-(CompactCoreKernel.extension b hb g).value x y‖ ≤ ‖f-g‖ := by
  have h3 := ContinuousMap.norm_coe_le_norm (f-g) (CompactCoreKernel.clamp b hb (x,y))
  rw [ContinuousMap.sub_apply] at h3
  exact h3

theorem reactionKernel_integral_eq (q : ℝ) (hq : 1≤q) (n r : ℕ) (ci : Coefficient) (b b' : ℝ) (hb' : 0<b')
    (hbb : b ≤ b') (hR : b'<(SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖ ≤ b') (i j : Fin 3)
    (hE : ∀ p : Region b',
      (CompactCoreKernel.extension b' hb' (SourcePairedCore.actualMap q hq n b' i j r)).value p.val.1 p.val.2=
        SourcePairedTensor.kernel q hq n r i j p.val) (v : VectorL2) :
    (∫ y : Space, ShellReactionIdentification.reactionKernel (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X x y i j*DynamicVolume.source ci v j y)=
      ∫ y : Space, (CompactCoreKernel.extension b' hb' (SourcePairedCore.actualMap q hq n b' i j r)).value x y*
        DynamicVolume.source ci v j y := by
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : ‖y‖ ≤ b
  · have hyR : ‖y‖<(SourcePairedInclusion.data q hq n r).R := hy.trans_lt (hbb.trans_lt hR)
    rw [SourcePairedReduction.reactionKernel_eq_pairedKernel q hq n r x y hyR i j]
    congr 1
    exact (hE ⟨(x,y),SourceCoreOperator.pair_mem_region b' x y hx (hy.trans hbb)⟩).symm
  · have h0 : ci.value (VectorFourier.coordinateMap y)=0 :=
      hci y (by simpa only [mem_closedBall,dist_zero_right] using hy)
    simp [DynamicVolume.source,h0]

theorem limitKernel_integral_eq (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (b b' : ℝ) (hb' : 0<b')
    (hbb : b ≤ b')
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (hx : ‖x‖ ≤ b') (i j : Fin 3) (v : VectorL2) :
    (∫ y : Space, VectorLimitIdentification.kernel q n i j (x,y)*DynamicVolume.source ci v j y)=
      ∫ y : Space, (CompactCoreKernel.extension b' hb' (SourcePairedCore.limitMap q hq n b' i j)).value x y*
        DynamicVolume.source ci v j y := by
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : ‖y‖ ≤ b
  · have hp := CompactCoreKernel.extension_actual b' hb' (SourcePairedCore.limitMap q hq n b' i j)
      ⟨(x,y),SourceCoreOperator.pair_mem_region b' x y hx (hy.trans hbb)⟩
    rw [SourcePairedCore.limitMap_apply q hq n b' hb'.le i j] at hp
    change (CompactCoreKernel.extension b' hb' (SourcePairedCore.limitMap q hq n b' i j)).value x y=_ at hp
    rw [hp]
  · have h0 : ci.value (VectorFourier.coordinateMap y)=0 :=
      hci y (by simpa only [mem_closedBall,dist_zero_right] using hy)
    simp [DynamicVolume.source,h0]

theorem reactionField_tendsto_uniform_compact (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b) (ρ0 : ℝ)
    (u : ℕ → VectorL2) (u0 : VectorL2) (hu : Tendsto u atTop (𝓝 u0)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖reactionField (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X (u r) x i-
        limitField q n ci u0 x i‖ ≤ ε := by
  have hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y)=0 :=
    SourcePairedReduction.inclusion_vanish ci d b hcar
  obtain ⟨b',hb'def⟩ : ∃ b' : ℝ, b'=max (max ρ0 b) 1 := ⟨_,rfl⟩
  have hb' : 0<b' := by rw [hb'def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρb : ρ0 ≤ b' := by rw [hb'def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hbb : b ≤ b' := by rw [hb'def]; exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨A0,hA0⟩ : ∃ A0 : ℝ, A0=Real.sqrt ci.bound*Real.sqrt (volume.real d.carrier) := ⟨_,rfl⟩
  have hs (v : VectorL2) (j : Fin 3) : Integrable (DynamicVolume.source ci v j) :=
    DynamicVolume.source_integrable ci v b hci j
  obtain ⟨bnd,hbnd_def⟩ : ∃ bnd : ℕ → Fin 3 → ℝ, bnd=fun r i => ∑ j : Fin 3,
    (‖SourcePairedCore.actualMap q hq n b' i j r-SourcePairedCore.limitMap q hq n b' i j‖*(A0*‖u r‖)+
      ‖SourcePairedCore.limitMap q hq n b' i j‖*(A0*‖u r-u0‖)) := ⟨_,rfl⟩
  have hbnd (i : Fin 3) : Tendsto (fun r => bnd r i) atTop (𝓝 0) := by
    have hnd : Tendsto (fun r => ‖u r-u0‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hu
    have hnu : Tendsto (fun r => ‖u r‖) atTop (𝓝 ‖u0‖) := hu.norm
    have hterm (j : Fin 3) : Tendsto (fun r => ‖SourcePairedCore.actualMap q hq n b' i j r-
        SourcePairedCore.limitMap q hq n b' i j‖*(A0*‖u r‖)+
        ‖SourcePairedCore.limitMap q hq n b' i j‖*(A0*‖u r-u0‖)) atTop (𝓝 (0*(A0*‖u0‖)+
          ‖SourcePairedCore.limitMap q hq n b' i j‖*(A0*0))) :=
      ((tendsto_iff_norm_sub_tendsto_zero.mp (SourcePairedCore.actualMap_limit q hq n b' hb'.le i j)).mul
        (tendsto_const_nhds.mul hnu)).add (tendsto_const_nhds.mul (tendsto_const_nhds.mul hnd))
    have := tendsto_finset_sum Finset.univ (fun j _ => hterm j)
    rw [hbnd_def]
    simpa using this
  have hbnd' : ∀ᶠ r : ℕ in atTop, ∀ i : Fin 3, bnd r i ≤ ε :=
    Filter.eventually_all.mpr (fun i => ((hbnd i).eventually (gt_mem_nhds hε)).mono (fun r h => h.le))
  have hent : ∀ᶠ r : ℕ in atTop, ∀ i j : Fin 3, ∀ p : Region b',
      (CompactCoreKernel.extension b' hb' (SourcePairedCore.actualMap q hq n b' i j r)).value p.val.1 p.val.2=
        SourcePairedTensor.kernel q hq n r i j p.val :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
      (fun j => SourcePairedCore.eventually_entries_actual q hq n b' hb' i j))
  have hrad : ∀ᶠ r : ℕ in atTop, b'<(SourcePairedInclusion.data q hq n r).R :=
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop b')
  filter_upwards [hbnd',hent,hrad] with r hbr he hR
  intro x hx i
  have hx' : ‖x‖ ≤ b' := hx.trans hρb
  refine le_trans ?_ (hbr i)
  rw [hbnd_def]
  unfold reactionField limitField
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [reactionKernel_integral_eq q hq n r ci b b' hb' hbb hR hci x hx' i j (he i j) (u r),
    limitKernel_integral_eq q hq n ci b b' hb' hbb hci x hx' i j u0]
  refine (split_bound _ _ _ _ (extension_diff_le b' hb' _ _) (fun x y => ContinuousMap.norm_coe_le_norm _ _)
    _ _ (hs (u r) j) (hs u0 j) x).trans ?_
  have m1 := source_mass' ci d (u r) j
  have m2 : (∫ y : Space, ‖DynamicVolume.source ci (u r) j y-DynamicVolume.source ci u0 j y‖) ≤
      A0*‖u r-u0‖ := by
    have he2 : (∫ y : Space, ‖DynamicVolume.source ci (u r) j y-DynamicVolume.source ci u0 j y‖)=
        ∫ y : Space, ‖DynamicVolume.source ci (u r-u0) j y‖ := by
      apply integral_congr_ae
      filter_upwards [source_sub_ae ci (u r) u0 j] with y hy
      rw [hy]
    rw [he2,hA0]
    exact source_mass' ci d (u r-u0) j
  rw [← hA0] at m1
  exact add_le_add (mul_le_mul_of_nonneg_left m1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left m2 (norm_nonneg _))

/-! ### Identification of the limit field with the parity plane reaction fields -/

theorem limitField_eq_potential (q : ℝ) (n : ℕ) (ci : Coefficient) (u : VectorL2) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y)=0)
    (x : Space) (i : Fin 3) :
    limitField q n ci u x i=(Complex.I/2)*
      ((((((q^(2*n) : ℝ) : ℂ)-1)+((((q^(2*n))⁻¹ : ℝ) : ℂ)-1))*
          HalfTurnReactionKernel.potential 1 (SourcePairedWallKernelAE.sourceField ci u) x i)+
        ((((q^(2*n) : ℝ) : ℂ)-1)-((((q^(2*n))⁻¹ : ℝ) : ℂ)-1))*
          HalfTurnReactionKernel.potential 1 (SourcePairedWallKernelAE.sourceField ci u) (-x) i) := by
  have hρ : ∀ j, Integrable (fun y => SourcePairedWallKernelAE.sourceField ci u y j) := fun j =>
    DynamicVolume.source_integrable ci u b hci j
  have h1 := HalfTurnReactionBridge.central_integral true 1 _ hρ x i
  have h2 := HalfTurnReactionBridge.central_integral false 1 _ hρ x i
  have hlin : limitField q n ci u x i=
      (((q^(2*n) : ℝ) : ℂ)-1)*(∑ j : Fin 3, ∫ y : Space,
        HalfTurnReactionBridge.central true 1 x y i j*SourcePairedWallKernelAE.sourceField ci u y j)+
      ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*(∑ j : Fin 3, ∫ y : Space,
        HalfTurnReactionBridge.central false 1 x y i j*SourcePairedWallKernelAE.sourceField ci u y j) := by
    unfold limitField
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have i1 := SourcePairedWallKernelAE.integrable_central true 1 _ hρ x i j
    have i2 := SourcePairedWallKernelAE.integrable_central false 1 _ hρ x i j
    rw [← integral_const_mul,← integral_const_mul,← integral_add (i1.const_mul _) (i2.const_mul _)]
    apply integral_congr_ae
    filter_upwards with y
    rw [HalfTurnReactionBridge.paired_kernel q n x y i j]
    simp only [SourcePairedWallKernelAE.sourceField]
    ring
  rw [hlin,h1,h2]
  simp only [if_true,Bool.false_eq_true,if_false]
  ring

theorem limitField_eq_parity (q : ℝ) (n : ℕ) (ci : Coefficient) (u : VectorL2) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y)=0)
    (hinv : HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci u))
    (x : Space) (i : Fin 3) :
    limitField q n ci u x i=
      (((q^(2*n) : ℝ) : ℂ)-1)*ParityPlaneFields.electric true 1 (DynamicVolume.source ci u) x i+
        ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*ParityPlaneFields.electric false 1 (DynamicVolume.source ci u) x i := by
  have hρ : ∀ j, Integrable (fun y => SourcePairedWallKernelAE.sourceField ci u y j) := fun j =>
    DynamicVolume.source_integrable ci u b hci j
  have hlin : limitField q n ci u x i=
      (((q^(2*n) : ℝ) : ℂ)-1)*(∑ j : Fin 3, ∫ y : Space,
        HalfTurnReactionBridge.central true 1 x y i j*SourcePairedWallKernelAE.sourceField ci u y j)+
      ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*(∑ j : Fin 3, ∫ y : Space,
        HalfTurnReactionBridge.central false 1 x y i j*SourcePairedWallKernelAE.sourceField ci u y j) := by
    unfold limitField
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have i1 := SourcePairedWallKernelAE.integrable_central true 1 _ hρ x i j
    have i2 := SourcePairedWallKernelAE.integrable_central false 1 _ hρ x i j
    rw [← integral_const_mul,← integral_const_mul,← integral_add (i1.const_mul _) (i2.const_mul _)]
    apply integral_congr_ae
    filter_upwards with y
    rw [HalfTurnReactionBridge.paired_kernel q n x y i j]
    simp only [SourcePairedWallKernelAE.sourceField]
    ring
  rw [hlin,HalfTurnReactionBridgeAE.central_eq_wall_ae true 1 _ hρ hinv x i,
    HalfTurnReactionBridgeAE.central_eq_wall_ae false 1 _ hρ hinv x i]
  rfl

end OQ14.SourcePairedReactionField
#print axioms OQ14.SourcePairedReactionField.reaction_eq_sqrt_reactionField
#print axioms OQ14.SourcePairedReactionField.paired_kernel_tendsto_uniform_compact
#print axioms OQ14.SourcePairedReactionField.source_mass'
#print axioms OQ14.SourcePairedReactionField.source_sub_ae
#print axioms OQ14.SourcePairedReactionField.norm_integral_mul_le
#print axioms OQ14.SourcePairedReactionField.reactionField_tendsto_uniform_compact
#print axioms OQ14.SourcePairedReactionField.limitField_eq_potential
#print axioms OQ14.SourcePairedReactionField.limitField_eq_parity
#print axioms OQ14.SourcePairedReactionField.kernel_continuous_slice
#print axioms OQ14.SourcePairedReactionField.split_bound
#print axioms OQ14.SourcePairedReactionField.extension_diff_le
#print axioms OQ14.SourcePairedReactionField.reactionKernel_integral_eq
#print axioms OQ14.SourcePairedReactionField.limitKernel_integral_eq
