import PolarMomentAE
import ComplexHarmonicBasis
import HalfTurnVectorAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ModalAngularSlices
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.PolarMomentEnergy OQ14.PolarMomentAE OQ14.ComplexHarmonicBasis
  OQ14.SphereHarmonicHilbert
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2
abbrev AngularL2 := ComplexHarmonicBasis.ComplexAmbient

def slice (u : VectorL2) (i : Fin 3) (r : ℝ) : AngularL2 := by
  classical
  exact if h : MemLp (fun ω : Sphere => DynamicConvolution.component i u (r • (ω : Space))) 2 angularMeasure then
    h.toLp (fun ω : Sphere => DynamicConvolution.component i u (r • (ω : Space)))
  else 0

theorem slice_actual_ae (u : VectorL2) (i : Fin 3) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      (slice u i r : Sphere → ℂ) =ᵐ[angularMeasure]
        fun ω => u (VectorFourier.coordinateMap (r • (ω : Space))) i := by
  have hm := slice_memLp_ae (DynamicConvolution.component i u)
  have hp := polar_ae (HalfTurnVectorAction.component_ae u i)
  filter_upwards [hm,hp] with r hr hp
  have hs : (slice u i r : Sphere → ℂ) =ᵐ[angularMeasure]
      fun ω => DynamicConvolution.component i u (r • (ω : Space)) := by
    simp only [slice, dif_pos hr]
    exact hr.coeFn_toLp
  exact hs.trans hp

theorem slice_expansion (u : VectorL2) (i : Fin 3) (r : ℝ) :
    HasSum (fun a : TotalIndex => ⟪vector a, slice u i r⟫ • vector a) (slice u i r) :=
  ComplexHarmonicBasis.expansion _

def coefficient (u : VectorL2) (i : Fin 3) (a : TotalIndex) (r : ℝ) : ℂ :=
  ⟪vector a, slice u i r⟫

theorem coefficient_actual_ae (u : VectorL2) (i : Fin 3) (a : TotalIndex) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), coefficient u i a r =
      ∫ ω : Sphere, ((SphereHarmonicBasis.angular a.1 a.2 ω : ℝ) : ℂ) *
        u (VectorFourier.coordinateMap (r • (ω : Space))) i ∂angularMeasure := by
  filter_upwards [slice_actual_ae u i] with r hr
  unfold coefficient
  rw [vector_toLp, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(complexAngular a).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure, hr] with ω hω hu
  change ((ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (complexAngular a)) : Sphere → ℂ) ω = ((SphereHarmonicBasis.angular a.1 a.2 ω : ℝ) : ℂ) at hω
  rw [hω, hu]
  simp [RCLike.inner_apply, mul_comm]

theorem coefficient_weighted_memLp (u : VectorL2) (i : Fin 3) (a : TotalIndex) :
    MemLp (fun r : ℝ => (r : ℂ) * coefficient u i a r) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  let σ : Sphere → ℂ := fun ω => ((SphereHarmonicBasis.angular a.1 a.2 ω : ℝ) : ℂ)
  have hσm : Measurable σ := (complexAngular a).continuous.measurable
  have hσ : MemLp σ 2 angularMeasure := by
    have hv := Lp.memLp (vector a)
    apply hv.ae_eq
    rw [vector_toLp]
    exact (complexAngular a).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure
  have hm := radial_moment_memLp (DynamicConvolution.component i u) σ hσm hσ
  apply hm.ae_eq
  filter_upwards [coefficient_actual_ae u i a, polar_ae (HalfTurnVectorAction.component_ae u i)] with r hc hr
  change (r : ℂ) * PolarMomentTesting.moment (DynamicConvolution.component i u) σ r = _
  rw [hc]
  congr 1
  unfold PolarMomentTesting.moment
  apply integral_congr_ae
  filter_upwards [hr] with ω hω
  rw [hω]
  dsimp [σ]
  ring

#print axioms OQ14.ModalAngularSlices.coefficient_weighted_memLp
#print axioms OQ14.ModalAngularSlices.slice_actual_ae
#print axioms OQ14.ModalAngularSlices.slice_expansion
#print axioms OQ14.ModalAngularSlices.coefficient_actual_ae
end OQ14.ModalAngularSlices



