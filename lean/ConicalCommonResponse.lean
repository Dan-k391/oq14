import ConicalTranslatedPotential

/-! Actual total source for one forced response of the common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonResponse
open MeasureTheory Set Metric OQ14.NewtonL2
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def totalSource (i : ι) (R T k : ℝ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
    (ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k) -
      ConicalCommonBaseline.forcing p a center i

def source (i : ι) (R T k : ℝ) (j : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
    (ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k) j x -
      ConicalCommonMaterial.source p a center i j x

omit [DecidableEq ι] in
theorem source_ae (i : ι) (R T k : ℝ) (j : Fin 3) :
    physicalCoordinate (totalSource p a center B hB hcontrast ha hsep i R T k) j =ᵐ[volume]
      source p a center B hB hcontrast ha hsep i R T k j :=
  ConicalResponseLinear.source_sub_ae _ _ _ _
    (StaticNewton.material_source_ae _ _)
    (ConicalCommonBaseline.source_ae p a center i) j

omit [DecidableEq ι] in
theorem source_zero_outer (i : ι) (R T k S : ℝ)
    (hS : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) S)
    (j : Fin 3) (x : Space) (hx : x ∉ closedBall (0 : Space) S) :
    source p a center B hB hcontrast ha hsep i R T k j x = 0 := by
  unfold source ConicalCommonBaseline.common
  rw [DynamicVolume.source_zero _ _ S
    (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep S hS) j x hx,
    ConicalCommonMaterial.source_zero_global_outer p a center i j S (hS i) x hx (ha i), sub_self]

omit [DecidableEq ι] in
theorem source_integrable (i : ι) (R T k S : ℝ)
    (hS : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) S) (j : Fin 3) :
    Integrable (source p a center B hB hcontrast ha hsep i R T k j) :=
  (DynamicVolume.source_integrable _ _ S
    (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep S hS) j).sub
    (ConicalCommonBaseline.source_integrable p a center i j S (hS i) (ha i))

omit [DecidableEq ι] in
theorem source_compact (i : ι) (R T k S : ℝ)
    (hS : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) S) (j : Fin 3) :
    HasCompactSupport (source p a center B hB hcontrast ha hsep i R T k j) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) S) isClosed_closedBall
    (source_zero_outer p a center B hB hcontrast ha hsep i R T k S hS j)

def electric (i : ι) (R T k : ℝ) : Maxwell.Field :=
  FieldResponse.electric k (totalSource p a center B hB hcontrast ha hsep i R T k)
    (source p a center B hB hcontrast ha hsep i R T k)

def magnetic (i : ι) (R T k : ℝ) : Maxwell.Field :=
  MagneticResponse.magnetic k (source p a center B hB hcontrast ha hsep i R T k)

def potential (i : ι) (R T k S : ℝ)
    (hS : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) S) :=
  ConicalCompactPotential.potentialData k S (totalSource p a center B hB hcontrast ha hsep i R T k)
    (source p a center B hB hcontrast ha hsep i R T k)
    (source_zero_outer p a center B hB hcontrast ha hsep i R T k S hS)
    (source_ae p a center B hB hcontrast ha hsep i R T k)

omit [DecidableEq ι] in
theorem field_ae (i : ι) (R T k : ℝ)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) (j : Fin 3) :
    physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j
      =ᵐ[volume.restrict (closedBall (0 : Space) R)]
        fun x => electric p a center B hB hcontrast ha hsep i R T k x j := by
  let c := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep
  let u := ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k
  let M := StaticCoefficient.sqrtMultiplier c u
  let F := ConicalCommonBaseline.forcing p a center i
  let A : VectorL2 →L[ℂ] VectorL2 := newtonOperator + DynamicConvolution.operator k (R+T)
  let D : VectorL2 →L[ℂ] VectorL2 := newtonOperator + DynamicConvolution.operator k (2*R)
  have hcR : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x) = 0 :=
    ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR
  have hcT : ∀ x : Space, x ∉ closedBall (0 : Space) T → c.value (VectorFourier.coordinateMap x) = 0 :=
    ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep T hT
  have hs := LocalVolumeResponse.electric_ae_on_ball k R R M (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hcR) (DynamicVolume.source_zero c u R hcR)
    (StaticNewton.material_source_ae c u) j
  have hl := LocalVolumeResponse.electric_ae_on_ball k R T M (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u T hcT) (DynamicVolume.source_zero c u T hcT)
    (StaticNewton.material_source_ae c u) j
  have hs' : physicalCoordinate (D M) j =ᵐ[volume.restrict (closedBall (0 : Space) R)]
      fun x => FieldResponse.electric k M (DynamicVolume.source c u) x j := by
    simpa only [D, LocalVolumeResponse.localRepresentative, two_mul, ContinuousLinearMap.add_apply] using hs
  have hl' : physicalCoordinate (A M) j =ᵐ[volume.restrict (closedBall (0 : Space) R)]
      fun x => FieldResponse.electric k M (DynamicVolume.source c u) x j := by
    simpa only [A, LocalVolumeResponse.localRepresentative, ContinuousLinearMap.add_apply] using hl
  let C := (ConicalBallRestriction.scalar R).comp (DynamicConvolution.component j)
  have hsame : C (D M) = C (A M) := by
    apply Lp.ext
    filter_upwards [ConicalBallRestriction.scalarRestriction_ae R (physicalCoordinate (D M) j),
      ConicalBallRestriction.scalarRestriction_ae R (physicalCoordinate (A M) j), hs', hl'] with x hd ha hs hl
    change ConicalBallRestriction.scalarRestriction R (physicalCoordinate (D M) j) x =
      ConicalBallRestriction.scalarRestriction R (physicalCoordinate (A M) j) x
    rw [hd, ha, hs, hl]
  have he := LocalVolumeResponse.electric_ae_on_ball k R T
    (totalSource p a center B hB hcontrast ha hsep i R T k)
    (source p a center B hB hcontrast ha hsep i R T k)
    (source_integrable p a center B hB hcontrast ha hsep i R T k T hT)
    (source_zero_outer p a center B hB hcontrast ha hsep i R T k T hT)
    (source_ae p a center B hB hcontrast ha hsep i R T k) j
  have hid : C (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) = C (A (M-F)) := by
    change C (-A F + D M) = C (A (M-F))
    rw [map_add, map_neg, map_sub, map_sub, hsame]
    abel
  have hlocal : physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j
      =ᵐ[volume.restrict (closedBall (0 : Space) R)] physicalCoordinate (A (M-F)) j := by
    filter_upwards [ConicalBallRestriction.scalarRestriction_ae R (physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j),
      ConicalBallRestriction.scalarRestriction_ae R (physicalCoordinate (A (M-F)) j)] with x hl hr
    have hx := congrArg (fun f : ConicalRungeBall.ScalarBall R => f x) hid
    change ConicalBallRestriction.scalarRestriction R (physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j) x =
      ConicalBallRestriction.scalarRestriction R (physicalCoordinate (A (M-F)) j) x at hx
    rwa [hl, hr] at hx
  exact hlocal.trans he

omit [DecidableEq ι] in
theorem material_relation (i : ι) (R T k : ℝ) (hR0 : 0 ≤ R)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) (j : Fin 3) :
    DynamicVolume.source (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k) j
        =ᵐ[volume.restrict (closedBall (0 : Space) R)] fun x =>
      ((ConicalCommonBaseline.common p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k x j := by
  let c := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep
  let u := ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k
  let E := ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae c E)
  rw [ConicalCommonDynamic.field_weighted p a center B hB hcontrast ha hsep i R T k hR0 hfreq] at hs
  filter_upwards [ae_restrict_of_ae hs,
    ae_restrict_of_ae (physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c u) j),
    ae_restrict_of_ae (StaticNewton.material_source_ae c u j),
    ae_restrict_of_ae (physicalCoordinate_ae E j), field_ae p a center B hB hcontrast ha hsep i R T k hR hT j] with x hs hm hsrc hf he
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * u (VectorFourier.coordinateMap x) j = _
  rw [← hsrc, hm, hs]
  change (c.value (VectorFourier.coordinateMap x) : ℂ) * E (VectorFourier.coordinateMap x) j = _
  rw [← hf, he]

theorem source_pairing_tip (i l : ι) (R T k : ℝ) (hR0 : 0 ≤ R)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (j : Fin 3) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ ball (center l) (a l)) :
    (∫ x, electric p a center B hB hcontrast ha hsep i R T k x j * f.val x) +
      (∫ x, source p a center B hB hcontrast ha hsep i R T k j x * f.val x) =
    ∫ x, (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
      electric p a center B hB hcontrast ha hsep i R T k x j * f.val x := by
  have hi : Integrable (fun x => electric p a center B hB hcontrast ha hsep i R T k x j * f.val x) :=
    FieldResponse.electric_test_integrable k _ _ (source_integrable p a center B hB hcontrast ha hsep i R T k T hT)
      (source_compact p a center B hB hcontrast ha hsep i R T k T hT) j f
  rw [← integral_add hi (PointSingularity.test_product_integrable _ _
    (source_integrable p a center B hB hcontrast ha hsep i R T k T hT j).locallyIntegrable
    f.val.continuous f.property)]
  apply integral_congr_ae
  have hm := (ae_restrict_iff' measurableSet_closedBall).mp
    (material_relation p a center B hB hcontrast ha hsep i R T k hR0 hfreq hR hT j)
  filter_upwards [hm] with x hx
  by_cases hz : f.val x = 0
  · simp [hz]
  · have ht : x ∈ ConicalCommonMaterial.materialBall a center l := ball_subset_closedBall (hf (subset_tsupport _ hz))
    have hxR := hR l (ConicalCommonMaterial.material_subset_outer p a center ha l ht)
    have hzero := ConicalCommonMaterial.source_zero_material p a center ha hsep hai i l j x ht
    rw [source, hx hxR, hzero, sub_zero, MaterialMaxwell.dielectric]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    ring

theorem maxwell_tip (i l : ι) (R T k : ℝ) (hR0 : 0 ≤ R)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (j : Fin 3) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ ball (center l) (a l)) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (electric p a center B hB hcontrast ha hsep i R T k)) j f =
      Complex.I*(k : ℂ)*MaterialMaxwell.fieldPair (magnetic p a center B hB hcontrast ha hsep i R T k) j f ∧
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p a center B hB hcontrast ha hsep i R T k)) j f =
      -(Complex.I*(k : ℂ)) * (∫ x, (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k x j * f.val x) := by
  constructor
  · exact MagneticResponse.electric_curl_pairing k _ _
      (source_integrable p a center B hB hcontrast ha hsep i R T k T hT)
      (source_compact p a center B hB hcontrast ha hsep i R T k T hT)
      (source_ae p a center B hB hcontrast ha hsep i R T k) j f
  · have h := MagneticResponse.magnetic_curl_pairing k
      (totalSource p a center B hB hcontrast ha hsep i R T k)
      (source p a center B hB hcontrast ha hsep i R T k)
      (source_integrable p a center B hB hcontrast ha hsep i R T k T hT)
      (source_compact p a center B hB hcontrast ha hsep i R T k T hT)
      (source_ae p a center B hB hcontrast ha hsep i R T k) j f
    change MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p a center B hB hcontrast ha hsep i R T k)) j f =
      -(Complex.I*(k : ℂ))*((∫ x, electric p a center B hB hcontrast ha hsep i R T k x j*f.val x)+
        (∫ x, source p a center B hB hcontrast ha hsep i R T k j x*f.val x)) at h
    rw [source_pairing_tip p a center B hB hcontrast ha hsep i l R T k hR0 hfreq hR hT hai j f hf] at h
    exact h

theorem gauss_tip (i l : ι) (R T k : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ ball (center l) (a l)) :
    (∑ j : Fin 3, ∫ x, (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
      electric p a center B hB hcontrast ha hsep i R T k x j * Maxwell.dcoord f.val x j) = 0 := by
  let Ω := ball (center l) (a l)
  let f' : RegionalMaxwellHelmholtz.Test Ω := ⟨f.val, f.val.smooth _, f.property, hf⟩
  let H := magnetic p a center B hB hcontrast ha hsep i R T k
  let D := fun x j => (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
    electric p a center B hB hcontrast ha hsep i R T k x j
  have hcurl (j : Fin 3) (g : RegionalMaxwellHelmholtz.Test Ω) :
      RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair H) j g =
        -(Complex.I*(k : ℂ)) * RegionalMaxwellHelmholtz.fieldPair D j g := by
    have hh := (maxwell_tip p a center B hB hcontrast ha hsep i l R T k hR0 hfreq hR hT hai j
      (ConicalInnerMaxwell.globalTest g) g.property.2.2).2
    exact hh
  exact RegionalMaxwellHelmholtz.divPair_zero_of_curl
    (RegionalMaxwellHelmholtz.fieldPair H) (RegionalMaxwellHelmholtz.fieldPair D)
    (-(Complex.I*(k : ℂ))) (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk))) hcurl f'

theorem gauss_centered (i l : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b < a l)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (f : 𝓢(Space, ℂ))
    (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ j : Fin 3, ∫ y, (ConicalLocalGauss.epsilon (p l) y : ℂ) *
      electric p a center B hB hcontrast ha hsep i R T k (center l + y) j * Maxwell.dcoord f y j) = 0 := by
  let g := NewtonConvolution.translate (-center l) f
  have hg : HasCompactSupport (g : Space → ℂ) := by
    apply HasCompactSupport.intro' (isCompact_closedBall (center l) b) isClosed_closedBall
    intro x hx
    change f (x + -center l) = 0
    apply image_eq_zero_of_nmem_tsupport
    intro ht
    have hn : ‖x - center l‖ < b := by simpa [sub_eq_add_neg] using hf ht
    apply hx
    simpa only [mem_closedBall, dist_eq_norm] using hn.le
  have hs' : tsupport (g : Space → ℂ) ⊆ ball (center l) (a l) := by
    have hc : tsupport (g : Space → ℂ) ⊆ closedBall (center l) b := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn
      have hz : g x = 0 := by
        change f (x + -center l) = 0
        apply image_eq_zero_of_nmem_tsupport
        intro ht
        have hn' : ‖x - center l‖ < b := by simpa [sub_eq_add_neg] using hf ht
        apply hn
        simpa only [mem_closedBall, dist_eq_norm] using hn'.le
      exact hx hz
    exact hc.trans (closedBall_subset_ball hb)
  have h := gauss_tip p a center B hB hcontrast ha hsep i l R T k hR0 hk hfreq hR hT hai ⟨g, hg⟩ hs'
  have he (j : Fin 3) : (∫ x : Space,
      (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k x j * Maxwell.dcoord g x j) =
      ∫ y : Space, (ConicalLocalGauss.epsilon (p l) y : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k (center l + y) j * Maxwell.dcoord f y j := by
    have ht := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k x j * Maxwell.dcoord g x j) (center l)
    rw [← ht]
    apply integral_congr_ae
    filter_upwards with y
    have hd : Maxwell.dcoord g (y + center l) j = Maxwell.dcoord f y j := by
      change GradientProjection.pderivative j g (y + center l) = _
      rw [show g = NewtonConvolution.translate (-center l) f from rfl, NewtonConvolution.translate_pderivative]
      simp only [NewtonConvolution.translate_apply, add_neg_cancel_right]
      rfl
    rw [hd]
    by_cases hy : y ∈ ball (0 : Space) b
    · have hya : y ∈ closedBall (0 : Space) (a l) := closedBall_subset_closedBall hb.le (ball_subset_closedBall hy)
      rw [show y + center l = center l + y by abel, ConicalCommonLocal.dielectric_local p a center B hB hcontrast ha hsep l (hai l) y hya]
    · have hn : y ∉ tsupport (f : Space → ℂ) := fun ht => hy (hf ht)
      simp [Maxwell.dcoord, fderiv_of_not_mem_tsupport ℝ hn]
  simpa only [he] using h

def centeredPotential (i l : ι) (R T k : ℝ)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) :=
  ConicalTranslatedPotential.translated (center l) (potential p a center B hB hcontrast ha hsep i R T k T hT)

def centeredCorrection (i l : ι) (R T k : ℝ) (x : Space) (j : Fin 3) : ℂ :=
  ElectricPotentialDecomposition.correction k (source p a center B hB hcontrast ha hsep i R T k) (x + center l) j

omit [DecidableEq ι] in
theorem centeredCorrection_continuous (i l : ι) (R T k : ℝ)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) (j : Fin 3) :
    Continuous (fun x => centeredCorrection p a center B hB hcontrast ha hsep i l R T k x j) :=
  (ElectricPotentialDecomposition.correction_continuous k T _ _
    (source_zero_outer p a center B hB hcontrast ha hsep i R T k T hT)
    (source_ae p a center B hB hcontrast ha hsep i R T k) j).comp (continuous_id.add continuous_const)

theorem centeredPotential_gauss (i l : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b < a l)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (f : 𝓢(Space, ℂ))
    (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ j : Fin 3, ∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
      ((centeredPotential p a center B hB hcontrast ha hsep i l R T k hT).derivative j x +
        centeredCorrection p a center B hB hcontrast ha hsep i l R T k x j) * Maxwell.dcoord f x j) = 0 := by
  have h := gauss_centered p a center B hB hcontrast ha hsep i l R T k b hR0 hk hb hfreq hR hT hai f hf
  have he (j : Fin 3) : (∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
      ((centeredPotential p a center B hB hcontrast ha hsep i l R T k hT).derivative j x +
        centeredCorrection p a center B hB hcontrast ha hsep i l R T k x j) * Maxwell.dcoord f x j) =
      ∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
        electric p a center B hB hcontrast ha hsep i R T k (center l + x) j * Maxwell.dcoord f x j := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [centeredPotential, ConicalTranslatedPotential.translated, potential,
      ConicalCompactPotential.potentialData, centeredCorrection, electric]
    rw [add_comm x (center l)]
    ring
  simpa only [he] using h

def tipSystem (i l : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b < a l)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) : ConicalProjectionData.System (p l) b :=
  ConicalProjectionLocalization.ofPotential (p l) b (hb.trans (hai l))
    (centeredPotential p a center B hB hcontrast ha hsep i l R T k hT)
    (centeredCorrection p a center B hB hcontrast ha hsep i l R T k)
    (centeredCorrection_continuous p a center B hB hcontrast ha hsep i l R T k hT)
    (centeredPotential_gauss p a center B hB hcontrast ha hsep i l R T k b hR0 hk hb hfreq hR hT hai)

theorem tipSystem_actual (i l : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b < a l)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (tipSystem p a center B hB hcontrast ha hsep i l R T k b hR0 hk hb hfreq hR hT hai) j x =
        electric p a center B hB hcontrast ha hsep i R T k (center l + x) j := by
  have h := ConicalProjectionLocalization.total_inner (p l) b (hb.trans (hai l))
    (centeredPotential p a center B hB hcontrast ha hsep i l R T k hT)
    (centeredCorrection p a center B hB hcontrast ha hsep i l R T k)
    (centeredCorrection_continuous p a center B hB hcontrast ha hsep i l R T k hT)
    (centeredPotential_gauss p a center B hB hcontrast ha hsep i l R T k b hR0 hk hb hfreq hR hT hai) j
  filter_upwards [h] with x hx hxb
  dsimp only [tipSystem]
  rw [hx hxb]
  dsimp [centeredPotential, ConicalTranslatedPotential.translated, potential,
    ConicalCompactPotential.potentialData, centeredCorrection, electric]
  rw [add_comm x (center l)]
  ring

end OQ14.ConicalCommonResponse
#print axioms OQ14.ConicalCommonResponse.source_ae
#print axioms OQ14.ConicalCommonResponse.source_zero_outer
#print axioms OQ14.ConicalCommonResponse.source_integrable
#print axioms OQ14.ConicalCommonResponse.source_compact
#print axioms OQ14.ConicalCommonResponse.potential
#print axioms OQ14.ConicalCommonResponse.field_ae
#print axioms OQ14.ConicalCommonResponse.material_relation
#print axioms OQ14.ConicalCommonResponse.source_pairing_tip
#print axioms OQ14.ConicalCommonResponse.maxwell_tip
#print axioms OQ14.ConicalCommonResponse.gauss_tip
#print axioms OQ14.ConicalCommonResponse.gauss_centered
#print axioms OQ14.ConicalCommonResponse.centeredCorrection_continuous
#print axioms OQ14.ConicalCommonResponse.centeredPotential_gauss
#print axioms OQ14.ConicalCommonResponse.tipSystem
#print axioms OQ14.ConicalCommonResponse.tipSystem_actual

