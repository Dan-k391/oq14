import HerglotzAngularL2
import FiniteVectorAngular
import FiniteHerglotzCaps
import FiniteCapApproximation
import ConicalEntireGauge

/-! Actual finite transverse harmonic Herglotz illuminations approximate smooth cap inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.FiniteAngularHerglotz
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis
open scoped ComplexInnerProductSpace Topology
abbrev Sphere := AngularPower.Sphere
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem normal_inner_dot (v : ComplexVectorSphere.Vector) (n : Sphere) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) v=
      dot (ConicalPlaneWaves.direction n) (fun i => v i) := by
  simp only [TransversePlaneFields.normal,PiLp.inner_apply,RCLike.inner_apply,
    ComplexVectorSphere.embed_apply,Complex.conj_ofReal,Fin.sum_univ_three,dot,
    ConicalPlaneWaves.direction]
  ring

theorem angular_tangent (m : ModeIndex) (n : Sphere) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (FiniteVectorAngular.angular m n)=0 := by
  have hreal : (∑ i : Fin 3,(n : Space) i*(FiniteVectorAngular.realAngular m n) i)=0 := by
    cases m with
    | inl a =>
      have h := VectorHarmonicNormalization.restriction_poloidal_tangent
        (representative (a.1+1) a.2) (a.1+1) (representative_homogeneous _ _) n
      simpa only [FiniteVectorAngular.realAngular,ContinuousMap.smul_apply,PiLp.smul_apply,
        smul_eq_mul,←Finset.mul_sum,mul_left_comm,mul_zero] using congrArg (fun x : ℝ => VectorHarmonicNormalization.normalizer a.1*x) h
    | inr a =>
      have h := VectorHarmonicNormalization.restriction_toroidal_tangent (representative (a.1+1) a.2) n
      simpa only [FiniteVectorAngular.realAngular,ContinuousMap.smul_apply,PiLp.smul_apply,
        smul_eq_mul,←Finset.mul_sum,mul_left_comm,mul_zero] using congrArg (fun x : ℝ => VectorHarmonicNormalization.normalizer a.1*x) h
  simp only [FiniteVectorAngular.angular,ContinuousMap.coe_mk,TransversePlaneFields.normal,
    PiLp.inner_apply,RCLike.inner_apply,ComplexVectorSphere.embed_apply,Complex.conj_ofReal,
    ←Complex.ofReal_mul,←Complex.ofReal_sum]
  simpa only [mul_comm] using congrArg (fun x : ℝ => (x : ℂ)) hreal

theorem amplitude_tangent (c : ModeIndex →₀ ℂ) (n : Sphere) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (FiniteVectorAngular.amplitude c n)=0 := by
  simp only [FiniteVectorAngular.amplitude,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    inner_sum,inner_smul_right,angular_tangent,mul_zero,Finset.sum_const_zero]

def incident (k : ℝ) (c : ModeIndex →₀ ℂ) : ConicalEntireGauge.Incident k where
  E := AngularHerglotz.electric k (fun n i => FiniteVectorAngular.amplitude c n i)
  H := AngularHerglotz.magnetic k (fun n i => FiniteVectorAngular.amplitude c n i)
  smoothE := AngularHerglotz.electric_smooth k _ (fun i =>
    (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).continuous.comp (FiniteVectorAngular.amplitude c).continuous)
  smoothH := AngularHerglotz.magnetic_smooth k _ (fun i =>
    (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).continuous.comp (FiniteVectorAngular.amplitude c).continuous)
  maxwell := AngularHerglotz.maxwell_at k _ (fun i =>
    (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ).continuous.comp (FiniteVectorAngular.amplitude c).continuous)
    (fun n => by rw [←normal_inner_dot]; exact amplitude_tangent c n)

theorem electric_value (k : ℝ) (c : ModeIndex →₀ ℂ) (x : Space) (i : Fin 3) :
    (incident k c).E x i=HerglotzAngularL2.value k x i (HerglotzAngularL2.finiteAmplitude c) := by
  change AngularHerglotz.electric k (fun n j => FiniteVectorAngular.amplitude c n j) x i=_
  rw [←HerglotzAngularL2.value_toLp k _ (amplitude_tangent c),FiniteVectorAngular.amplitude_toLp]
  rfl

def capMap (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) :
    C(Sphere,ComplexVectorSphere.Vector) :=
  ⟨fun n => (WithLp.equiv 2 (Fin 3 → ℂ)).symm (FiniteHerglotzCaps.amplitude c r hr n),
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
      (continuous_pi (FiniteHerglotzCaps.amplitude_continuous c r hr))⟩

theorem capMap_tangent (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (n : Sphere) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (capMap c r hr n)=0 := by
  rw [normal_inner_dot]
  exact FiniteHerglotzCaps.amplitude_tangent c r hr n

theorem uniform_cap_approximation (c : ConicalRungeClosure.WaveIndex →₀ ℂ)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ModeIndex →₀ ℂ, ∀ (k : ℝ) (x : Space) (i : Fin 3),
      ‖(incident k d).E x i-FiniteHerglotzCaps.electric k c r hr x i‖ < ε := by
  have ht : ComplexVectorSphere.IsTangential (ContinuousMap.toLp 2 angularMeasure ℂ (capMap c r hr)) := by
    filter_upwards [(capMap c r hr).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hn
    rw [hn]
    exact capMap_tangent c r hr n
  obtain ⟨d,hd⟩ := HerglotzAngularL2.uniform_finite_approximation _ ht ε hε
  refine ⟨d,?_⟩
  intro k x i
  rw [electric_value]
  have he := HerglotzAngularL2.value_toLp k _ (capMap_tangent c r hr) x i
  have hb := hd k x i
  rw [he] at hb
  exact hb

theorem uniform_plane_approximation (k R : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ModeIndex →₀ ℂ, ∀ x ∈ closedBall (0 : Space) R, ∀ i : Fin 3,
      ‖(incident k d).E x i-ConicalFinitePlanes.electric k c x i‖ < ε := by
  obtain ⟨r,hr,hcap⟩ := FiniteCapApproximation.uniform_electric_approximation k R c (ε/2) (by positivity)
  obtain ⟨d,hd⟩ := uniform_cap_approximation c r hr (ε/2) (by positivity)
  refine ⟨d,?_⟩
  intro x hx i
  have he : (incident k d).E x i-ConicalFinitePlanes.electric k c x i=
      ((incident k d).E x i-FiniteHerglotzCaps.electric k c r hr x i)+
        (FiniteHerglotzCaps.electric k c r hr x i-ConicalFinitePlanes.electric k c x i) := by ring
  rw [he]
  exact (norm_add_le _ _).trans_lt ((add_lt_add (hd k x i) (hcap r hr le_rfl x hx i)).trans_eq (by ring))

end OQ14.FiniteAngularHerglotz
#print axioms OQ14.FiniteAngularHerglotz.normal_inner_dot
#print axioms OQ14.FiniteAngularHerglotz.angular_tangent
#print axioms OQ14.FiniteAngularHerglotz.amplitude_tangent
#print axioms OQ14.FiniteAngularHerglotz.electric_value
#print axioms OQ14.FiniteAngularHerglotz.capMap_tangent
#print axioms OQ14.FiniteAngularHerglotz.uniform_cap_approximation
#print axioms OQ14.FiniteAngularHerglotz.uniform_plane_approximation
