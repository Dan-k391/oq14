import ModalAngularSlices
import ComplexTransverseExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalVectorAngularSlices
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.PolarIntegration OQ14.PolarMomentAE OQ14.ComplexVectorSphere
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

def physical (u : VectorL2) : Lp ComplexVectorSphere.Vector 2 (volume : Measure Space) :=
  Lp.compMeasurePreservingₗᵢ ℂ VectorFourier.coordinateMap VectorFourier.coordinateMap_preserving u

theorem physical_ae (u : VectorL2) : (physical u : Space → ComplexVectorSphere.Vector) =ᵐ[volume]
    fun x => u (VectorFourier.coordinateMap x) :=
  Lp.coeFn_compMeasurePreserving u VectorFourier.coordinateMap_preserving

theorem slice_memLp_ae (u : VectorL2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      MemLp (fun n : Sphere => physical u (r • (n : Space))) 2 angularMeasure := by
  let f := physical u
  have hf2 : Integrable (fun x : Space => ‖f x‖^2) := (Lp.memLp f).norm.integrable_sq
  have hp := (ComplexPolarIntegration.integrable_polar_product _ hf2).prod_left_ae
  have hs : ∀ᵐ r : Radius ∂radialMeasure, MemLp (fun n : Sphere => f ((r : ℝ) • (n : Space))) 2 angularMeasure := by
    filter_upwards [hp] with r hr
    have hm : StronglyMeasurable (fun n : Sphere => f ((r : ℝ) • (n : Space))) :=
      (Lp.stronglyMeasurable f).comp_measurable (continuous_const.smul continuous_subtype_val).measurable
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hr
  have hd : Measurable (fun r : Radius => ENNReal.ofReal ((r : ℝ)^2)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2)
  have hb : ∀ᵐ r : Radius ∂(volume.comap ((↑) : Radius → ℝ)),
      MemLp (fun n : Sphere => f ((r : ℝ) • (n : Space))) 2 angularMeasure := by
    have hh := (ae_withDensity_iff hd).mp hs
    filter_upwards [hh] with r hr
    exact hr (ENNReal.ofReal_pos.mpr (sq_pos_of_pos r.property)).ne'
  exact (ae_restrict_iff_subtype measurableSet_Ioi).mpr hb

def slice (u : VectorL2) (r : ℝ) : ComplexVectorSphere.Ambient := by
  classical
  exact if h : MemLp (fun n : Sphere => physical u (r • (n : Space))) 2 angularMeasure then
    h.toLp (fun n : Sphere => physical u (r • (n : Space))) else 0

theorem slice_actual_ae (u : VectorL2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      (slice u r : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure]
        fun n => u (VectorFourier.coordinateMap (r • (n : Space))) := by
  have hm := slice_memLp_ae u
  have hp := polar_ae (physical_ae u)
  filter_upwards [hm,hp] with r hr hp
  have hs : (slice u r : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure]
      fun n => physical u (r • (n : Space)) := by
    simp only [slice, dif_pos hr]
    exact hr.coeFn_toLp
  exact hs.trans hp

theorem embed_norm (x : Space) : ‖embedVector x‖ = ‖x‖ := by
  have h : ‖embedVector x‖^2 = ‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp [embed_apply, Complex.norm_real]
  nlinarith [norm_nonneg (embedVector x), norm_nonneg x]

def tangentFunction (F : ComplexVectorSphere.Ambient) (n : Sphere) : ComplexVectorSphere.Vector :=
  F n - ⟪embedVector (n : Space), F n⟫ • embedVector (n : Space)

theorem tangent_memLp (F : ComplexVectorSphere.Ambient) :
    MemLp (tangentFunction F) 2 angularMeasure := by
  have hn : StronglyMeasurable (fun n : Sphere => embedVector (n : Space)) :=
    (embedVector.continuous.comp continuous_subtype_val).stronglyMeasurable
  have hf := Lp.stronglyMeasurable F
  have hm : AEStronglyMeasurable (tangentFunction F) angularMeasure :=
    (hf.sub ((hn.inner hf).smul hn)).aestronglyMeasurable
  apply (Lp.memLp F).of_le_mul (c := 2) hm
  filter_upwards with n
  have hnorm : ‖embedVector (n : Space)‖ = 1 := by rw [embed_norm, sphere_norm]
  have hi := norm_inner_le_norm (𝕜 := ℂ) (embedVector (n : Space)) (F n)
  rw [hnorm, one_mul] at hi
  unfold tangentFunction
  calc
    ‖F n - ⟪embedVector (n : Space), F n⟫ • embedVector (n : Space)‖ ≤
        ‖F n‖ + ‖⟪embedVector (n : Space), F n⟫ • embedVector (n : Space)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖F n‖ := by rw [norm_smul, hnorm, mul_one] ; nlinarith

def tangent (F : ComplexVectorSphere.Ambient) : ComplexVectorSphere.Ambient :=
  (tangent_memLp F).toLp (tangentFunction F)

theorem tangent_actual (F : ComplexVectorSphere.Ambient) :
    (tangent F : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure] tangentFunction F :=
  (tangent_memLp F).coeFn_toLp

theorem tangent_isTangential (F : ComplexVectorSphere.Ambient) : IsTangential (tangent F) := by
  filter_upwards [tangent_actual F] with n hn
  rw [hn]
  have hnorm : ‖embedVector (n : Space)‖ = 1 := by rw [embed_norm, sphere_norm]
  have hself : ⟪embedVector (n : Space), embedVector (n : Space)⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  simp [tangentFunction, inner_sub_right, inner_smul_right, hself]

theorem transverse_expansion (u : VectorL2) (r : ℝ) :
    HasSum (fun a : ComplexTransverseExpansion.ModeIndex =>
      ⟪ComplexTransverseExpansion.vector a, tangent (slice u r)⟫ • ComplexTransverseExpansion.vector a)
      (tangent (slice u r)) :=
  ComplexTransverseExpansion.expansion _ (tangent_isTangential _)

def radialFunction (F : ComplexVectorSphere.Ambient) (n : Sphere) : ℂ :=
  ⟪embedVector (n : Space), F n⟫

theorem radial_memLp (F : ComplexVectorSphere.Ambient) : MemLp (radialFunction F) 2 angularMeasure := by
  have hn : StronglyMeasurable (fun n : Sphere => embedVector (n : Space)) :=
    (embedVector.continuous.comp continuous_subtype_val).stronglyMeasurable
  have hm : AEStronglyMeasurable (radialFunction F) angularMeasure :=
    (hn.inner (Lp.stronglyMeasurable F)).aestronglyMeasurable
  apply (Lp.memLp F).of_le hm
  filter_upwards with n
  have hi := norm_inner_le_norm (𝕜 := ℂ) (embedVector (n : Space)) (F n)
  rw [embed_norm, sphere_norm, one_mul] at hi
  exact hi

def radial (F : ComplexVectorSphere.Ambient) : ComplexHarmonicBasis.ComplexAmbient :=
  (radial_memLp F).toLp (radialFunction F)

theorem radial_actual (F : ComplexVectorSphere.Ambient) :
    (radial F : Sphere → ℂ) =ᵐ[angularMeasure] radialFunction F := (radial_memLp F).coeFn_toLp

theorem radial_expansion (u : VectorL2) (r : ℝ) :
    HasSum (fun a : SphereHarmonicHilbert.TotalIndex =>
      ⟪ComplexHarmonicBasis.vector a, radial (slice u r)⟫ • ComplexHarmonicBasis.vector a)
      (radial (slice u r)) := ComplexHarmonicBasis.expansion _

theorem vector_decomposition_ae (F : ComplexVectorSphere.Ambient) :
    ∀ᵐ n : Sphere ∂angularMeasure,
      F n = tangent F n + (radial F n) • embedVector (n : Space) := by
  filter_upwards [tangent_actual F, radial_actual F] with n ht hr
  rw [ht, hr]
  simp [tangentFunction, radialFunction]

#print axioms OQ14.ModalVectorAngularSlices.vector_decomposition_ae
#print axioms OQ14.ModalVectorAngularSlices.radial_expansion
#print axioms OQ14.ModalVectorAngularSlices.transverse_expansion
#print axioms OQ14.ModalVectorAngularSlices.tangent_isTangential
#print axioms OQ14.ModalVectorAngularSlices.slice_memLp_ae
#print axioms OQ14.ModalVectorAngularSlices.slice_actual_ae
end OQ14.ModalVectorAngularSlices



