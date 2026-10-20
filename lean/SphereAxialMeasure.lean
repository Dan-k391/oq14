import AxialCoordinates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Deriving the actual angular measure formula from Euclidean cones and the actual Jacobian. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OQ14.SphereAxialMeasure
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.AxialCoordinates
open scoped Topology Pointwise ENNReal

def angularDomain : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi

theorem angularDomain_open : IsOpen angularDomain := isOpen_Ioo.prod isOpen_Ioo

@[fun_prop] theorem transverse_continuous : Continuous transverse :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

def direction (q : angularDomain) : Sphere := ⟨physical ![1,q.val.1,q.val.2], by
  rw [mem_sphere, dist_zero_right, physical_norm _ (show ![1,q.val.1,q.val.2] ∈ domain from
    ⟨by norm_num,q.property.1,q.property.2⟩)]
  rfl⟩

theorem direction_continuous : Continuous direction := by
  apply Continuous.subtype_mk
  unfold physical
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [AxialCoordinates.map] using
      (show Continuous (fun q : angularDomain => transverse q.val.1*Real.cos q.val.2) by fun_prop)
  · simpa [AxialCoordinates.map] using
      (show Continuous (fun q : angularDomain => transverse q.val.1*Real.sin q.val.2) by fun_prop)
  · simpa [AxialCoordinates.map] using
      (show Continuous (fun q : angularDomain => q.val.1) by fun_prop)

def split : Coordinates ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

theorem split_apply (p : Coordinates) : split p = (p 0,(p 1,p 2)) := rfl

theorem split_symm (r z θ : ℝ) : split.symm (r,(z,θ)) = ![r,z,θ] := by
  apply split.injective
  rw [split.apply_symm_apply,split_apply]
  rfl

theorem split_preserving : MeasurePreserving split := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  exact h2.comp h1

theorem physical_scale (p : Coordinates) (hp : p ∈ domain) :
    physical p = p 0 • (direction ⟨(p 1,p 2),hp.2⟩ : Space) := by
  ext i
  fin_cases i <;> simp [physical,direction,AxialCoordinates.map] <;> ring

def cone (s : Set Sphere) : Set Space := Ioo (0 : ℝ) 1 • (Subtype.val '' s)

theorem cone_radial (s : Set Sphere) (r : ℝ) (hr : 0 < r) (n : Sphere) :
    r • (n : Space) ∈ cone s ↔ r < 1 ∧ n ∈ s := by
  constructor
  · rintro ⟨b,hb,y,⟨m,hm,rfl⟩,he⟩
    have hn := congrArg norm he
    simp only [norm_smul, Real.norm_eq_abs, sphere_norm, mul_one,
      abs_of_pos hb.1,abs_of_pos hr] at hn
    subst b
    have hm' := congrArg (fun x : Space => r⁻¹ • x) he
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] at hm'
    have he' : m=n := Subtype.ext hm'
    exact ⟨hb.2,he' ▸ hm⟩
  · rintro ⟨hr1,hn⟩
    exact ⟨r,⟨hr,hr1⟩,n,⟨n,hn,rfl⟩,rfl⟩

theorem cone_measurable (s : Set Sphere) (hs : MeasurableSet s) : MeasurableSet (cone s) := by
  let r : Ioi (0 : ℝ) := ⟨1,by norm_num⟩
  have hV : MeasurableSet (homeomorphUnitSphereProd Space ⁻¹' (s ×ˢ Iio r)) :=
    (homeomorphUnitSphereProd Space).measurable (hs.prod measurableSet_Iio)
  have hm := (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space)).compl).measurableSet_image.mpr hV
  convert hm using 1
  change Ioo (0 : ℝ) 1 • (Subtype.val '' s) =
    Subtype.val '' (homeomorphUnitSphereProd Space ⁻¹' (s ×ˢ Iio r))
  symm
  rw [← image2_smul,image2_image_right,← Homeomorph.image_symm,image_image,
    ← image_subtype_val_Ioi_Iio r,image2_image_left,image2_swap,← image_prod]
  rfl

def parameterMeasure : Measure angularDomain := (volume : Measure (ℝ × ℝ)).comap Subtype.val

theorem parameter_set_measurable (s : Set Sphere) (hs : MeasurableSet s) :
    MeasurableSet (Subtype.val '' (direction ⁻¹' s) : Set (ℝ × ℝ)) :=
  (MeasurableEmbedding.subtype_coe angularDomain_open.measurableSet).measurableSet_image.mpr
    (direction_continuous.measurable hs)

theorem parameterMeasure_apply (s : Set Sphere) :
    parameterMeasure (direction ⁻¹' s) = volume (Subtype.val '' (direction ⁻¹' s)) :=
  (MeasurableEmbedding.subtype_coe angularDomain_open.measurableSet).comap_apply _ _

theorem radial_factor : (∫⁻ r : ℝ in Ioo (0 : ℝ) 1, ENNReal.ofReal (r^2)) = 1/3 := by
  have hi : IntegrableOn (fun r : ℝ => r^2) (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegral.intervalIntegrable_pow (n := 2) (a := (0 : ℝ)) (b := 1)).1.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun r => sq_nonneg r))]
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num [integral_pow, ENNReal.ofReal_div_of_pos]

theorem cone_volume (s : Set Sphere) (hs : MeasurableSet s) :
    volume (cone s) = (1/3 : ℝ≥0∞)*parameterMeasure (direction ⁻¹' s) := by
  let A : Set (ℝ × ℝ) := Subtype.val '' (direction ⁻¹' s)
  let C : Set Coordinates := VectorFourier.coordinateMap.symm ⁻¹' cone s
  have hA : MeasurableSet A := parameter_set_measurable s hs
  have hC : MeasurableSet C := VectorFourier.coordinateMap.symm.measurable (cone_measurable s hs)
  have hAsub : A ⊆ angularDomain := by rintro q ⟨p,_,rfl⟩; exact p.property
  have hAmem (p : Coordinates) (hp : p ∈ domain) :
      (p 1,p 2) ∈ A ↔ direction ⟨(p 1,p 2),hp.2⟩ ∈ s := by
    constructor
    · rintro ⟨q,hq,he⟩
      have he' : q = (⟨(p 1,p 2),hp.2⟩ : angularDomain) := Subtype.ext he
      simpa only [he'] using hq
    · intro h
      exact ⟨⟨(p 1,p 2),hp.2⟩,h,rfl⟩
  have hmem (p : Coordinates) (hp : p ∈ domain) :
      AxialCoordinates.map p ∈ C ↔ p 0 < 1 ∧ (p 1,p 2) ∈ A := by
    change physical p ∈ cone s ↔ _
    rw [physical_scale p hp,cone_radial s (p 0) hp.1,hAmem p hp]
  let B : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun q =>
    (Ioo (0 : ℝ) 1).indicator (fun r => ENNReal.ofReal (r^2)) q.1 * A.indicator 1 q.2
  have he (p : Coordinates) : domain.indicator
      (fun p => ENNReal.ofReal ((p 0)^2)*C.indicator 1 (AxialCoordinates.map p)) p = B (split p) := by
    simp only [B,split_apply]
    by_cases hp : p ∈ domain
    · rw [indicator_of_mem hp]
      by_cases hr : p 0 < 1 <;> by_cases hq : (p 1,p 2) ∈ A <;>
        simp [hmem p hp,hr,hq,show 0 < p 0 from hp.1]
    · rw [indicator_of_not_mem hp]
      by_cases hr : p 0 ∈ Ioo (0 : ℝ) 1
      · by_cases hq : (p 1,p 2) ∈ A
        · exact (hp ⟨hr.1,hAsub hq⟩).elim
        · simp [hq]
      · simp [hr]
  have hrmeas : Measurable ((Ioo (0 : ℝ) 1).indicator (fun r : ℝ => ENNReal.ofReal (r^2))) := by
    exact (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).indicator measurableSet_Ioo
  have hB : Measurable (A.indicator (1 : ℝ × ℝ → ℝ≥0∞)) := measurable_const.indicator hA
  calc
    volume (cone s) = volume C :=
      ((MeasurePreserving.symm VectorFourier.coordinateMap VectorFourier.coordinateMap_preserving).measure_preimage_equiv (cone s)).symm
    _ = ∫⁻ p, C.indicator (1 : Coordinates → ℝ≥0∞) p := (lintegral_indicator_one hC).symm
    _ = ∫⁻ p in domain, ENNReal.ofReal ((p 0)^2)*C.indicator 1 (AxialCoordinates.map p) :=
      lintegral_coordinates _
    _ = ∫⁻ p, B (split p) := by rw [← lintegral_indicator domain_open.measurableSet]; exact lintegral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∫⁻ q, B q := split_preserving.lintegral_comp_emb split.measurableEmbedding B
    _ = (1/3 : ℝ≥0∞)*volume A := by
      rw [show (volume : Measure (ℝ × (ℝ × ℝ))) = (volume : Measure ℝ).prod volume from rfl]
      rw [lintegral_prod_mul hrmeas.aemeasurable hB.aemeasurable,
        lintegral_indicator measurableSet_Ioo,lintegral_indicator_one hA,radial_factor]
    _ = _ := by rw [parameterMeasure_apply]

theorem direction_preserving : MeasurePreserving direction parameterMeasure angularMeasure := by
  refine ⟨direction_continuous.measurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply direction_continuous.measurable hs]
  change parameterMeasure (direction ⁻¹' s) = (volume : Measure Space).toSphere s
  rw [Measure.toSphere_apply' _ hs]
  change parameterMeasure (direction ⁻¹' s) = (Module.finrank ℝ Space : ℝ≥0∞)*volume (cone s)
  have hd : Module.finrank ℝ Space = 3 := by simp [Space,FourierL2.Space]
  rw [hd,cone_volume s hs,← mul_assoc]
  norm_num [ENNReal.mul_inv_cancel]

theorem lintegral_direction (f : Sphere → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ n, f n ∂angularMeasure) = ∫⁻ q, f (direction q) ∂parameterMeasure :=
  (direction_preserving.lintegral_comp hf).symm

theorem integral_direction (f : Sphere → ℝ) (hf : Integrable f angularMeasure) :
    (∫ n, f n ∂angularMeasure) = ∫ q, f (direction q) ∂parameterMeasure := by
  have hm : AEStronglyMeasurable f (Measure.map direction parameterMeasure) := by
    rw [direction_preserving.map_eq]
    exact hf.aestronglyMeasurable
  rw [← direction_preserving.map_eq]
  exact integral_map direction_preserving.measurable.aemeasurable hm

theorem integrable_axial (f : Space → ℝ) (hf : Integrable (fun n : Sphere => f n) angularMeasure) :
    IntegrableOn (fun q : ℝ × ℝ => f (physical ![1,q.1,q.2])) angularDomain volume := by
  have hp : Integrable (fun q => f (direction q : Space)) parameterMeasure :=
    (direction_preserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  rw [IntegrableOn,← map_comap_subtype_coe angularDomain_open.measurableSet]
  exact (MeasurableEmbedding.subtype_coe angularDomain_open.measurableSet).integrable_map_iff.mpr hp

theorem integral_axial (f : Space → ℝ) (hf : Integrable (fun n : Sphere => f n) angularMeasure) :
    (∫ n : Sphere, f n ∂angularMeasure) =
      ∫ q in angularDomain, f (physical ![1,q.1,q.2]) := by
  rw [integral_direction _ hf]
  exact integral_subtype_comap angularDomain_open.measurableSet
    (fun q : ℝ × ℝ => f (physical ![1,q.1,q.2]))

theorem integral_axial_iterated (f : Space → ℝ) (hf : Integrable (fun n : Sphere => f n) angularMeasure) :
    (∫ n : Sphere, f n ∂angularMeasure) =
      ∫ z in Ioo (-1 : ℝ) 1, ∫ θ in Ioo (-Real.pi) Real.pi, f (physical ![1,z,θ]) := by
  rw [integral_axial f hf]
  exact setIntegral_prod _ (integrable_axial f hf)

theorem latitude_null (t : ℝ) : angularMeasure {n : Sphere | (n : Space) 2 = t} = 0 := by
  let S : Set Sphere := {n | (n : Space) 2 = t}
  have hs : MeasurableSet S :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp continuous_subtype_val).measurable
      (measurableSet_singleton t)
  have hz : (volume : Measure (ℝ × ℝ)) ({t} ×ˢ univ) = 0 := by
    change ((volume : Measure ℝ).prod volume) ({t} ×ˢ univ) = 0
    rw [Measure.prod_prod]
    simp
  change angularMeasure S = 0
  rw [← direction_preserving.measure_preimage hs.nullMeasurableSet,parameterMeasure_apply]
  apply measure_mono_null _ hz
  rintro q ⟨p,hp,rfl⟩
  constructor
  · change p.val.1 ∈ ({t} : Set ℝ)
    simpa [S,direction,physical,AxialCoordinates.map] using hp
  · exact mem_univ _

end OQ14.SphereAxialMeasure

#print axioms OQ14.SphereAxialMeasure.angularDomain_open
#print axioms OQ14.SphereAxialMeasure.transverse_continuous
#print axioms OQ14.SphereAxialMeasure.direction_continuous
#print axioms OQ14.SphereAxialMeasure.split_apply
#print axioms OQ14.SphereAxialMeasure.split_symm
#print axioms OQ14.SphereAxialMeasure.split_preserving
#print axioms OQ14.SphereAxialMeasure.physical_scale
#print axioms OQ14.SphereAxialMeasure.cone_radial
#print axioms OQ14.SphereAxialMeasure.cone_measurable
#print axioms OQ14.SphereAxialMeasure.parameter_set_measurable
#print axioms OQ14.SphereAxialMeasure.parameterMeasure_apply
#print axioms OQ14.SphereAxialMeasure.radial_factor
#print axioms OQ14.SphereAxialMeasure.cone_volume
#print axioms OQ14.SphereAxialMeasure.direction_preserving
#print axioms OQ14.SphereAxialMeasure.lintegral_direction
#print axioms OQ14.SphereAxialMeasure.integral_direction
#print axioms OQ14.SphereAxialMeasure.integrable_axial
#print axioms OQ14.SphereAxialMeasure.integral_axial
#print axioms OQ14.SphereAxialMeasure.integral_axial_iterated
#print axioms OQ14.SphereAxialMeasure.latitude_null
