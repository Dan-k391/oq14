import ConicalInteriorResponse
import SourcePairedPlaneIdentification

/-! The dyadic integral representative of the field response of a compactly supported source away from the
support, on an arbitrary open set where the source vanishes (the earlier statements are for balls centred at the
origin and for strips).  The static Newton part is identified with the Hessian integral against the source by the
cut-off kernel pairing on small balls, and the balls cover the open set countably.  Applied to the combined
shell-plus-inclusion polarization this identifies the physical `L2` scattered field with the continuous dyadic
integral almost everywhere on the core off the closure of the inclusion carrier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ExteriorMaterialOffCarrier
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.GreenKernel OQ14.NewtonExteriorResponse
open scoped Topology SchwartzMap

/-! ### Newton part away from the support -/

theorem weakConvolution_sep_pairing (ρ : Space → ℂ) (hρ : Integrable ρ) (δ S : ℝ) (hδ : 0 < δ)
    (hc : ∀ y, y ∉ closedBall (0 : Space) S → ρ y = 0) (i j : Fin 3) (f : DynamicSource.Test)
    (hsep : ∀ x ∈ tsupport (f.val : Space → ℂ), ∀ y, ρ y ≠ 0 → δ ≤ ‖x - y‖) :
    NewtonConvolution.weakConvolution ρ i j f.val =
      ∫ x, KernelConvolution.response (awayKernel δ i j) ρ x * f.val x := by
  rw [KernelConvolution.response_pairing _ _ (awayKernel_locallyIntegrable δ hδ i j)
    hρ (source_compact ρ S hc) f]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ y = 0
  · simp only [hz, zero_mul]
  have hfy : y ∉ tsupport (f.val : Space → ℂ) := by
    intro h
    have := hsep y h y hz
    simp only [sub_self, norm_zero] at this
    linarith
  rw [FieldResponse.weakHessian_symmetric i j, NewtonExterior.translated_weakHessian_away i j f y hfy]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f.val x = 0
  · simp only [hx, mul_zero]
  have hs := hsep x (subset_tsupport _ hx) y hz
  simp [awayKernel, hs]

theorem newton_cutResponse_pairing_sep (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ S : ℝ) (hδ : 0 < δ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (i : Fin 3) (f : DynamicSource.Test)
    (hsep : ∀ j, ∀ x ∈ tsupport (f.val : Space → ℂ), ∀ y, ρ j y ≠ 0 → δ ≤ ‖x - y‖) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * f.val x) =
      ∫ x, cutResponse δ ρ x i * f.val x := by
  rw [NewtonL1L2.newtonOperator_spatial_pairing F (fun j => (hρ j).congr (hF j).symm)]
  simp only [cutResponse, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => FieldResponse.response_test_integrable _ (ρ j)
    (awayKernel_locallyIntegrable δ hδ i j) (hρ j) (source_compact _ S (hc j)) f)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← weakConvolution_sep_pairing (ρ j) (hρ j) δ S hδ (hc j) i j f (hsep j)]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards [hF j] with y hy
  rw [hy]

theorem newton_ae_cutResponse_ball (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ S : ℝ) (hδ : 0 < δ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (c : Space) (b : ℝ) (hsep : ∀ j, ∀ x ∈ ball c b, ∀ y, ρ j y ≠ 0 → δ ≤ ‖x - y‖) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball c b →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x = cutResponse δ ρ x i := by
  have hN := (Lp.memLp (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i)).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hC := cutResponse_locallyIntegrable F ρ hρ hF δ S hδ hc i
  have hz := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x - cutResponse δ ρ x i)
    ((hN.sub hC).locallyIntegrableOn (ball c b))
  have hh : ∀ (g : Space → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ ball c b →
      (∫ x, g x • (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x -
        cutResponse δ ρ x i)) = 0 := by
    intro g hg hgc hgU
    have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left (g := Complex.ofReal) (by simp)
    let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz (fun x => (g x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg) hgc', hgc'⟩
    have hs : tsupport (f.val : Space → ℂ) = tsupport g := by
      change closure (Function.support (fun x => (g x : ℂ))) = closure (Function.support g)
      ext x
      simp [Function.support]
    have hp := newton_cutResponse_pairing_sep F ρ hρ hF δ S hδ hc i f
      (fun j x hx y hy => hsep j x ((hs ▸ hgU) hx) y hy)
    have hn := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
    have hd := cutResponse_test_integrable ρ hρ δ S hδ hc i f
    have he : (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * f.val x -
        cutResponse δ ρ x i * f.val x) = 0 := by
      rw [integral_sub hn hd, hp, sub_self]
    convert he using 1
    apply integral_congr_ae
    filter_upwards with x
    change (g x : ℂ) * (_ - _) = _ * (g x : ℂ) - _ * (g x : ℂ)
    ring
  filter_upwards [hz hh] with x hx hm
  exact sub_eq_zero.mp (hx hm)

theorem newton_ae_ball (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (c : Space) (a b : ℝ) (hba : b < a) (hi : ∀ j y, y ∈ ball c a → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball c b →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x =
        ∑ j, ∫ y, ρ j y * phiHessian 0 (x - y) i j := by
  have hd : 0 < (a - b) / 2 := by linarith
  have hsep : ∀ j, ∀ x ∈ ball c b, ∀ y, ρ j y ≠ 0 → (a - b) / 2 ≤ ‖x - y‖ := by
    intro j x hx y hy
    have hya : a ≤ dist y c := by
      by_contra h
      exact hy (hi j y (mem_ball.mpr (not_le.mp h)))
    have hxb : dist x c < b := mem_ball.mp hx
    have h1 : dist y c ≤ dist y x + dist x c := dist_triangle y x c
    have h2 : ‖x - y‖ = dist y x := by rw [dist_comm, dist_eq_norm]
    rw [h2]
    linarith
  filter_upwards [newton_ae_cutResponse_ball F ρ hρ hF ((a - b) / 2) S hd hc c b hsep i] with x hx hm
  rw [hx hm]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ j y = 0
  · simp only [hz, zero_mul]
  · simp [awayKernel, hsep j x hm y hz]

theorem newton_ae_open (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ U →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x =
        ∑ j, ∫ y, ρ j y * phiHessian 0 (x - y) i j := by
  have key : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x (2 * r) ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨ε / 2, by linarith, by
      have : 2 * (ε / 2) = ε := by ring
      rw [this]
      exact hsub⟩
  choose! r hr hsub using key
  obtain ⟨t, htU, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := U) (f := fun x => ball x (r x))
    (fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx)))
  have hball : ∀ᵐ x : Space, ∀ c ∈ t, x ∈ ball c (r c) →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x =
        ∑ j, ∫ y, ρ j y * phiHessian 0 (x - y) i j := by
    rw [ae_ball_iff htc]
    intro c hct
    exact newton_ae_ball F ρ hρ hF S hc c (2 * r c) (r c) (by linarith [hr c (htU hct)])
      (fun j y hy => hi j y (hsub c (htU hct) hy)) i
  filter_upwards [hball] with x hx hxU
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (hcov hxU)
  exact hx c hct hxc

/-! ### The field response on an open set where the source vanishes -/

theorem source_excluded_open (ρ : Space → ℂ) (U : Set Space) (hU : IsOpen U)
    (hi : ∀ y ∈ U, ρ y = 0) (x : Space) (hx : x ∈ U) : x ∉ tsupport ρ := by
  apply not_mem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hi y hy

theorem electric_ae_open (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ U →
      FieldResponse.electric k F ρ x i = ExteriorContinuity.electric k ρ x i := by
  filter_upwards [newton_ae_open F ρ hρ hF S hc U hU hi i] with x hx hm
  simp only [FieldResponse.electric, hx hm, ← Finset.sum_add_distrib, ExteriorContinuity.electric]
  apply Finset.sum_congr rfl
  intro j _
  have hn := source_excluded_open (ρ j) U hU (hi j) x hm
  have hcompact := source_compact (ρ j) S (hc j)
  rw [KernelConvolution.response, ← integral_add
    (ConicalInteriorResponse.source_integrand_integrable _ (ρ j)
      (NewtonExterior.hessian_continuousAt 0 i j) (hρ j) hcompact x hn)
    (ConicalInteriorResponse.source_integrand_integrable _ (ρ j)
      (remainder_continuousAt k i j) (hρ j) hcompact x hn)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [DyadicKernel.remainder]
  ring

/-! ### The scattered field of the combined solution off the carrier -/

/-- **The physical scattered field off the carrier.**  For the combined coefficient `add cs ci` (shell supported in
`Rin ≤ |x| ≤ X`, inclusion supported in the closed ball of radius `b < Rin` and vanishing off the set `K`), the
`L2` scattered field of every solution equals almost everywhere, at the points of the core `|x| < Rin` outside the
closure of `K`, the literal dyadic integral of the combined polarization. -/
theorem scattered_ae_off_carrier (cs ci : StaticCoefficient.Coefficient) (b Rin X : ℝ) (hbR : b < Rin)
    (hRX : Rin ≤ X)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (K : Set Space) (hK : ∀ y : Space, y ∉ K → ci.value (VectorFourier.coordinateMap y) = 0)
    (hd : ShellInclusionVolume.Disjoint cs ci) (u : VectorFourier.VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, ‖x‖ < Rin → x ∉ closure K →
      MaterialField.scattered (ShellInclusionVolume.add cs ci) 1 u x i =
        ExteriorContinuity.electric 1 (DynamicVolume.source (ShellInclusionVolume.add cs ci) u) x i := by
  have hcsX : ∀ y : Space, y ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => hcs y (fun h => hy h.1)
  have hciX : ∀ y : Space, y ∉ closedBall (0 : Space) X → ci.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => hci y (fun h => hy (closedBall_subset_closedBall (hbR.le.trans hRX) h))
  have hρs := fun j => DynamicVolume.source_integrable cs u X hcsX j
  have hρi := fun j => DynamicVolume.source_integrable ci u b hci j
  have hFs := StaticNewton.material_source_ae cs u
  have hFi := StaticNewton.material_source_ae ci u
  have hi_s : ∀ j y, y ∈ ball (0 : Space) Rin → DynamicVolume.source cs u j y = 0 := by
    intro j y hy
    unfold DynamicVolume.source
    rw [hcs y (fun h => h.2 hy)]
    simp
  have hi_i : ∀ j y, y ∈ (closure K)ᶜ → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    unfold DynamicVolume.source
    rw [hK y (fun h => hy (subset_closure h))]
    simp
  have hint := ConicalInteriorResponse.electric_ae_interior 1 (StaticCoefficient.sqrtMultiplier cs u)
    (DynamicVolume.source cs u) hρs hFs Rin X (DynamicVolume.source_zero cs u X hcsX) hi_s
  have hext := electric_ae_open 1 (StaticCoefficient.sqrtMultiplier ci u)
    (DynamicVolume.source ci u) hρi hFi b (DynamicVolume.source_zero ci u b hci) (closure K)ᶜ
    isClosed_closure.isOpen_compl hi_i i
  have hrs : ∀ᵐ x : Space, ∀ j : Fin 3, x ∈ closedBall (0 : Space) X →
      Integrable (fun y => DyadicKernel.remainder 1 (x - y) i j * DynamicVolume.source cs u j y) :=
    ae_all_iff.mpr (fun j => DynamicVolume.remainder_source_integrable_ae cs u 1 X hcsX i j)
  have hri : ∀ᵐ x : Space, ∀ j : Fin 3, x ∈ closedBall (0 : Space) X →
      Integrable (fun y => DyadicKernel.remainder 1 (x - y) i j * DynamicVolume.source ci u j y) :=
    ae_all_iff.mpr (fun j => DynamicVolume.remainder_source_integrable_ae ci u 1 X hciX i j)
  filter_upwards [hint, hext, hrs, hri,
    Lp.coeFn_add (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier cs u)) i)
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier ci u)) i)]
    with x h1 h2 h3 h4 h5 hxR hxK
  have h1' := congrFun (h1 (mem_ball_zero_iff.mpr hxR)) i
  have h2' := h2 hxK
  have hxX : x ∈ closedBall (0 : Space) X := mem_closedBall_zero_iff.mpr (hxR.le.trans hRX)
  have hsrc (j : Fin 3) : DynamicVolume.source (ShellInclusionVolume.add cs ci) u j =ᵐ[volume]
      fun y => DynamicVolume.source cs u j y + DynamicVolume.source ci u j y :=
    Filter.Eventually.of_forall (fun y => SourcePairedPlaneIdentification.source_add_disjoint cs ci hd u j y)
  have hsplitR := SourcePairedPlaneIdentification.response_sum_split (fun j z => DyadicKernel.remainder 1 z i j) x _ _
    (ShellInclusionVolume.add cs ci) u u u hsrc
    (fun j => by simpa only [mul_comm] using h3 j hxX)
    (fun j => by simpa only [mul_comm] using h4 j hxX)
  have hsplitD := SourcePairedPlaneIdentification.response_sum_split (fun j z => DyadicKernel.dyadic 1 z i j) x _ _
    (ShellInclusionVolume.add cs ci) u u u hsrc
    (fun j => CoreMaterialEvaluation.actual_integrand_integrable cs Rin X hcs x hxR i j u)
    (fun j => ConicalInteriorResponse.source_integrand_integrable
      (fun z => DyadicKernel.dyadic 1 z i j) (DynamicVolume.source ci u j)
      (fun z hz => ExteriorContinuity.dyadic_continuousAt 1 i j z hz) (hρi j)
      (source_compact _ b (DynamicVolume.source_zero ci u b hci j)) x
      (source_excluded_open _ _ isClosed_closure.isOpen_compl (hi_i j) x hxK))
  unfold MaterialField.scattered FieldResponse.electric at *
  rw [ShellInclusionVolume.sqrtMultiplier_add cs ci hd, ContinuousLinearMap.add_apply, map_add,
    SourcePairedPlaneIdentification.physicalCoordinate_add, h5]
  change (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier cs u)) i x +
    NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier ci u)) i x) +
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add cs ci) u j) x = _
  rw [hsplitR]
  have eE : ExteriorContinuity.electric 1 (DynamicVolume.source (ShellInclusionVolume.add cs ci) u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add cs ci) u j) x := rfl
  rw [eE, hsplitD]
  have eS : ExteriorContinuity.electric 1 (DynamicVolume.source cs u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source cs u j) x := rfl
  have eI : ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source ci u j) x := rfl
  rw [eS] at h1'
  rw [eI] at h2'
  linear_combination h1' + h2'

/-! ### The physical total electric field of the combined solution off the carrier -/

/-- **The physical total electric field off the carrier.**  The `L2` class `MaterialField.total` of the combined
solution equals, almost everywhere on the set of core points (`|x| < R_r`) outside the closure of the carrier of
the inclusion, the assembled plane electric field.  This extends the identification on the gap annulus
`b < |x| < R_r` to the whole core off the carrier closure. -/
theorem combined_total_electric_ae_off_carrier (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)
    (ci : StaticCoefficient.Coefficient) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (d : BoundedMaterialKernel.SupportData ci)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b))
    (inc : Maxwell.Field) (fs fi : VectorFourier.VectorL2)
    (hfi : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    ∀ᵐ x : Space, ‖x‖ < (SourcePairedInclusion.data q hq n r).R → x ∉ closure d.carrier → ∀ i : Fin 3,
      MaterialField.total (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
            (SourcePairedInclusion.data q hq n r).X (fs + fi)) inc x i =
        SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
            (SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
              (SourcePairedInclusion.data q hq n r).X fs fi))
          (SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
            (SourcePairedInclusion.data q hq n r).X inc fs) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hae := ae_all_iff.mpr (fun i : Fin 3 => scattered_ae_off_carrier
    (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hb
    (SourcePairedInclusion.radii_ordered q hq n r)
    (SourcePairedPlaneIdentification.shell_hcs q hq n r) hci d.carrier d.carrierZero hd
    (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X (fs + fi)) i)
  filter_upwards [hae] with x hx hxR hxK i
  have hη : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ d.carrier, ε ≤ ‖x - y‖ := by
    by_contra h
    push_neg at h
    apply hxK
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hlt⟩ := h ε hε
    exact ⟨y, hy, by rwa [dist_eq_norm]⟩
  obtain ⟨ε, hε, hxη⟩ := hη
  have h := SourcePairedPlaneIdentification.combined_total_electric_eq q hq n r ci b hb hci d hE inc fs fi
    hfi hfs ε hε x hxR hxη i
  unfold MaterialField.total
  rw [hx i hxR hxK]
  exact h

/-- The identification on a neighbourhood of every point of the core off the carrier closure: the set of core
points outside the closure of the carrier is open, and on it the physical `L2` total electric field is almost
everywhere equal to the assembled plane electric field. -/
theorem combined_total_electric_ae_restrict (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)
    (ci : StaticCoefficient.Coefficient) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (d : BoundedMaterialKernel.SupportData ci)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b))
    (inc : Maxwell.Field) (fs fi : VectorFourier.VectorL2)
    (hfi : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) (i : Fin 3) :
    IsOpen {x : Space | ‖x‖ < (SourcePairedInclusion.data q hq n r).R ∧ x ∉ closure d.carrier} ∧
    (fun x => MaterialField.total (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
            (SourcePairedInclusion.data q hq n r).X (fs + fi)) inc x i) =ᵐ[volume.restrict
        {x : Space | ‖x‖ < (SourcePairedInclusion.data q hq n r).R ∧ x ∉ closure d.carrier}]
      (fun x => SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
            (SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
              (SourcePairedInclusion.data q hq n r).X fs fi))
          (SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
            (SourcePairedInclusion.data q hq n r).X inc fs) x i) := by
  have hopen : IsOpen {x : Space | ‖x‖ < (SourcePairedInclusion.data q hq n r).R ∧ x ∉ closure d.carrier} :=
    (isOpen_lt continuous_norm continuous_const).inter isClosed_closure.isOpen_compl
  refine ⟨hopen, ?_⟩
  have hmain := combined_total_electric_ae_off_carrier q hq n r ci b hb hci d hE inc fs fi hfi hfs
  exact (ae_restrict_iff' hopen.measurableSet).mpr (hmain.mono fun x hx hxV => hx hxV.1 hxV.2 i)

end OQ14.ExteriorMaterialOffCarrier
#print axioms OQ14.ExteriorMaterialOffCarrier.scattered_ae_off_carrier
#print axioms OQ14.ExteriorMaterialOffCarrier.combined_total_electric_ae_off_carrier
#print axioms OQ14.ExteriorMaterialOffCarrier.weakConvolution_sep_pairing
#print axioms OQ14.ExteriorMaterialOffCarrier.newton_cutResponse_pairing_sep
#print axioms OQ14.ExteriorMaterialOffCarrier.newton_ae_cutResponse_ball
#print axioms OQ14.ExteriorMaterialOffCarrier.newton_ae_ball
#print axioms OQ14.ExteriorMaterialOffCarrier.newton_ae_open
#print axioms OQ14.ExteriorMaterialOffCarrier.source_excluded_open
#print axioms OQ14.ExteriorMaterialOffCarrier.electric_ae_open
#print axioms OQ14.ExteriorMaterialOffCarrier.combined_total_electric_ae_restrict
