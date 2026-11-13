import Packet04TMProjection
import Packet04ToroidalMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04TMMoments
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolarMomentEnergy OQ14.PolarMomentTesting
  OQ14.Packet04ToroidalMoments OQ14.ComplexSphereMaxwell
open scoped Topology

/-- Toroidal coefficient of the actual magnetic response, using its local
L² representative on the ball of radius T. -/
def magneticCoefficient (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  ∑ j : Fin 3, moment (ComplexMagneticResponse.response
    (ModalWeightedMode.coefficient n hn) z 1 T u j) (weight p j) r

theorem magneticCoefficient_local (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    LocallyIntegrableOn (magneticCoefficient n hn z T u p) (Ioi (0 : ℝ)) := by
  have hi (j : Fin 3) := Packet01MomentIntegrability.moment_locallyIntegrableOn
    (ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u j)
    (weight p j) (weight_continuous p j).measurable (weight_memLp p j)
  have he : magneticCoefficient n hn z T u p = (fun r =>
      moment (ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u 0) (weight p 0) r +
      moment (ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u 1) (weight p 1) r +
      moment (ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u 2) (weight p 2) r) := by
    ext r; simp [magneticCoefficient, Fin.sum_univ_three]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem magneticCoefficient_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) T),
      magneticCoefficient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        magnetic n hn z u (r • (ω : Space)) j * weight p j ω ∂angularMeasure := by
  let V := ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (V j))
  have hv : ∀ᵐ x : Space ∂volume, x ∈ closedBall 0 T → ∀ j : Fin 3,
      V j x = magnetic n hn z u x j :=
    (ae_restrict_iff' measurableSet_closedBall).mp (ae_all_iff.mpr (fun j =>
      ComplexMagneticResponse.response_actual (ModalWeightedMode.coefficient n hn) z 1 T u
        (ModalWeightedMode.coefficient_support n hn) j))
  have hp := PolarMomentAE.polar_ae hv
  have hi' := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1) hi
  have hp' := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1) hp
  filter_upwards [hi', hp', ae_restrict_mem measurableSet_Ioo] with r hr he hri
  change (∑ j : Fin 3, ∫ ω : Sphere, V j (r • (ω : Space)) * weight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      V j (r • (ω : Space)) * weight p j ω) angularMeasure :=
    (hr j).integrable_mul (weight_memLp p j)
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [he] with ω hω
  have hx : r • (ω : Space) ∈ closedBall (0 : Space) T := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hri.1, sphere_norm, mul_one]
    exact hri.2.le
  apply Finset.sum_congr rfl
  intro j _
  rw [hω hx j]

/-- L² coordinates of the actual electric displacement. -/
def displacementCoordinates (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (j : Fin 3) : FourierL2.ScalarL2 :=
  NewtonL2.physicalCoordinate (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) j +
    NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier
      (ModalWeightedMode.coefficient n hn) u) j

def displacementRadial (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  HarmonicMomentIntegrability.radialMoment (displacementCoordinates n hn z T u) p r

theorem displacementRadial_local (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    LocallyIntegrableOn (displacementRadial n hn z T u p) (Ioi (0 : ℝ)) :=
  Packet01MomentIntegrability.radialMoment_locallyIntegrableOn _ p

theorem displacementCoordinates_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (j : Fin 3) :
    (displacementCoordinates n hn z T u j : Space → ℂ) =ᵐ[volume]
      fun x => Packet04WeakSphereMaxwell.permittivity n hn x * electric n hn z T u x j := by
  filter_upwards [Lp.coeFn_add
      (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response
        (ModalWeightedMode.coefficient n hn) z 1 T u) j)
      (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier
        (ModalWeightedMode.coefficient n hn) u) j),
    NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) j,
    StaticNewton.material_source_ae (ModalWeightedMode.coefficient n hn) u j,
    ComplexSphereInterface.source_actual n hn z T hT u hker j] with x ha he hs hr
  change _ = (1 + ((ModalWeightedMode.coefficient n hn).value
    (VectorFourier.coordinateMap x) : ℂ)) * _
  unfold displacementCoordinates
  rw [ha]
  simp only [Pi.add_apply]
  change _ = DynamicVolume.source (ModalWeightedMode.coefficient n hn) u j x at hs
  rw [he, hs, hr]
  dsimp [electric]
  ring

theorem displacementRadial_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      displacementRadial n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        (Packet04WeakSphereMaxwell.permittivity n hn (r • (ω : Space)) *
          electric n hn z T u (r • (ω : Space)) j) *
            HarmonicMomentCoupling.radialWeight p j ω ∂angularMeasure := by
  let D := displacementCoordinates n hn z T u
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (D j))
  have he := ae_all_iff.mpr (fun j : Fin 3 =>
    PolarMomentAE.polar_ae (displacementCoordinates_actual n hn z T hT u hker j))
  filter_upwards [hi, he] with r hr he
  change (∑ j : Fin 3, ∫ ω : Sphere, D j (r • (ω : Space)) *
    HarmonicMomentCoupling.radialWeight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      D j (r • (ω : Space)) * HarmonicMomentCoupling.radialWeight p j ω) angularMeasure :=
    (hr j).integrable_mul (HarmonicMomentCoupling.weight_memLp p j).1
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Finset.sum_congr rfl
  intro j _
  rw [hω j]

/-- Scalar radial-test identity for actual magnetic and displacement moments. -/
theorem magnetic_displacement_weak (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r *
      magneticCoefficient n hn z T u p r) =
    -(I*z) * ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * (r : ℂ) *
      displacementRadial n hn z T u p r := by
  have hh := Packet04TMProjection.actual_magnetic_radial_polar n hn z T hT u hker
    η hη hc hs p l hp
  have hmag : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Ioo (0 : ℝ) T →
      magneticCoefficient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        magnetic n hn z u (r • (ω : Space)) j * weight p j ω ∂angularMeasure := by
    have h := (ae_restrict_iff' measurableSet_Ioo).mp (magneticCoefficient_actual n hn z T u p)
    exact ae_restrict_of_ae h
  have hd := displacementRadial_actual n hn z T hT u hker p
  have hl : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, magnetic n hn z u (r • (ω : Space)) i *
        (η r * (r : ℂ)^l * DebyeRadialTrace.angularToroidal p (ω : Space) i)
        ∂angularMeasure) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * magneticCoefficient n hn z T u p r := by
    apply integral_congr_ae
    filter_upwards [hmag, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    by_cases hrt : r < T
    · rw [hr ⟨hr0, hrt⟩]
      simp only [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [weight]
      simp only [pow_add]
      ring
    · have hz : η r = 0 := image_eq_zero_of_nmem_tsupport (fun ht => hrt (hs ht).2)
      simp [hz]
  have hright : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, (Packet04WeakSphereMaxwell.permittivity n hn (r • (ω : Space)) *
        electric n hn z T u (r • (ω : Space)) i) *
        ((r : ℂ) * ((ω : Space) i : ℂ) * (η r * (r : ℂ)^l *
          complexEvaluate p (ω : Space))) ∂angularMeasure) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * (r : ℂ) *
        displacementRadial n hn z T u p r := by
    apply integral_congr_ae
    filter_upwards [hd] with r hr
    rw [hr]
    simp only [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [HarmonicMomentCoupling.radialWeight, SphericalMomentEquation.angularPolynomial]
    simp only [pow_add]
    ring
  rw [hl, hright] at hh
  exact hh

/-- The magnetic toroidal coefficient equals minus iz times radius times the
actual radial displacement coefficient, almost everywhere through r=1. -/
theorem magnetic_displacement_coefficient (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) T),
      magneticCoefficient n hn z T u p r =
        -(I*z)*(r : ℂ)*displacementRadial n hn z T u p r := by
  let M := magneticCoefficient n hn z T u p
  let D := displacementRadial n hn z T u p
  let g := fun r : ℝ => (r : ℂ)^(l+2) * (M r + I*z*(r : ℂ)*D r)
  have hm := (magneticCoefficient_local n hn z T u p).mono_set
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hd := (displacementRadial_local n hn z T u p).mono_set
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hg : LocallyIntegrableOn g (Ioo (0 : ℝ) T) := by
    have hr := hd.continuousOn_mul Complex.continuous_ofReal.continuousOn isOpen_Ioo.isLocallyClosed
    have hc : ContinuousOn (fun _ : ℝ => I*z) (Ioo (0 : ℝ) T) := continuousOn_const
    have ha := hm.add (hr.continuousOn_mul hc isOpen_Ioo.isLocallyClosed)
    convert ha.continuousOn_mul (Complex.continuous_ofReal.pow (l+2)).continuousOn isOpen_Ioo.isLocallyClosed using 1
    ext r
    dsimp [g, M, D]
    ring
  have ha : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) T → g r = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hg (by
      intro η hη hc hs
      have hηc : ContDiff ℝ (⊤ : ℕ∞) (fun r => (η r : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
      have hcc : HasCompactSupport (fun r => (η r : ℂ)) := hc.comp_left (by simp : Complex.ofReal 0 = 0)
      have hsc : tsupport (fun r => (η r : ℂ)) ⊆ Ioo (0 : ℝ) T := by
        have he : tsupport (fun r => (η r : ℂ)) = tsupport η := by
          apply congrArg closure; ext r; exact not_congr Complex.ofReal_eq_zero
        rwa [he]
      have hw := magnetic_displacement_weak n hn z T hT u hker p l hp
        (fun r => (η r : ℂ)) hηc hcc hsc
      have hiM : IntegrableOn (fun r : ℝ => (r : ℂ)^(l+2) * (η r : ℂ) * M r) (Ioi 0) := by
        have hi (j : Fin 3) := HarmonicMomentIntegrability.radial_integrable
          (ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u j)
          (weight p j) (weight_continuous p j) (weight_memLp p j)
          (fun r => (η r : ℂ)) hηc hcc (l+1)
        change Integrable (fun r : ℝ => (r : ℂ)^(l+2) * (η r : ℂ) * M r) (volume.restrict (Ioi 0))
        convert (hi 0).add ((hi 1).add (hi 2)) using 1
        funext r
        dsimp [M, magneticCoefficient]
        simp only [Fin.sum_univ_three]
        ring
      have hiD : IntegrableOn (fun r : ℝ => (r : ℂ)^(l+2) * (η r : ℂ) * (r : ℂ) * D r) (Ioi 0) := by
        have hi (j : Fin 3) := HarmonicMomentIntegrability.radial_integrable
          (displacementCoordinates n hn z T u j) (HarmonicMomentCoupling.radialWeight p j)
          (HarmonicMomentIntegrability.radial_weight_continuous p j)
          (HarmonicMomentCoupling.weight_memLp p j).1
          (fun r => (η r : ℂ)) hηc hcc (l+2)
        change Integrable (fun r : ℝ => (r : ℂ)^(l+2) * (η r : ℂ) * (r : ℂ) * D r) (volume.restrict (Ioi 0))
        convert (hi 0).add ((hi 1).add (hi 2)) using 1
        funext r
        dsimp [D, displacementRadial, HarmonicMomentIntegrability.radialMoment]
        simp only [Fin.sum_univ_three, pow_succ]
        ring
      have hsum : (∫ r in Ioi (0 : ℝ), (η r : ℂ) * g r) = 0 := by
        have heq : (fun r : ℝ => (η r : ℂ) * g r) =
            fun r : ℝ => (r : ℂ)^(l+2) * (η r : ℂ) * M r +
              (I*z)*((r : ℂ)^(l+2) * (η r : ℂ) * (r : ℂ) * D r) := by
          funext r; dsimp [g]; ring
        rw [heq, integral_add hiM (hiD.const_mul _), integral_const_mul, hw]
        ring
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hsum
      · simpa only [Complex.real_smul, mul_comm] using hsum
      · intro r hr
        have hz : η r = 0 := image_eq_zero_of_nmem_tsupport (fun ht => hr (hs ht).1)
        simp [hz])
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr ha,
    ae_restrict_mem measurableSet_Ioo] with r hr hri
  have hz : (r : ℂ)^(l+2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hri.1.ne')
  have hh := (mul_eq_zero.mp hr).resolve_left hz
  change M r = -(I*z)*(r : ℂ)*D r
  linear_combination hh

def displacementGradient (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  HarmonicMomentIntegrability.gradientMoment (displacementCoordinates n hn z T u) p r

theorem displacementGradient_local (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    LocallyIntegrableOn (displacementGradient n hn z T u p) (Ioi (0 : ℝ)) :=
  Packet01MomentIntegrability.gradientMoment_locallyIntegrableOn _ p

theorem displacementGradient_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      displacementGradient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        (Packet04WeakSphereMaxwell.permittivity n hn (r • (ω : Space)) *
          electric n hn z T u (r • (ω : Space)) j) *
            HarmonicMomentCoupling.gradientWeight p j ω ∂angularMeasure := by
  let D := displacementCoordinates n hn z T u
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (D j))
  have he := ae_all_iff.mpr (fun j : Fin 3 =>
    PolarMomentAE.polar_ae (displacementCoordinates_actual n hn z T hT u hker j))
  filter_upwards [hi, he] with r hr he
  change (∑ j : Fin 3, ∫ ω : Sphere, D j (r • (ω : Space)) *
    HarmonicMomentCoupling.gradientWeight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      D j (r • (ω : Space)) * HarmonicMomentCoupling.gradientWeight p j ω) angularMeasure :=
    (hr j).integrable_mul (HarmonicMomentCoupling.weight_memLp p j).2
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Finset.sum_congr rfl
  intro j _
  rw [hω j]

/-- The actual gradient-test projection, in scalar weak-derivative form. -/
theorem magnetic_gradient_weak (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * deriv η r *
      magneticCoefficient n hn z T u p r) =
      I*z * ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r *
        displacementGradient n hn z T u p r := by
  let F := Packet04TMProjection.gradientVectorTest T η hη hc hs p
  have ht : (fun y j => (F j).val y) =
      fun y j => η ‖y‖ * dcoord (complexEvaluate p) y j := by
    funext y j
    simp [F, Packet04TMProjection.gradientVectorTest, RadialNormTest.radialNorm,
      complexEvaluate_partial, complexEvaluate]
  have h1 := Packet04VectorTests.vector_integrable (ball (0 : Space) T)
    (magnetic n hn z u) (ComplexMagneticHelmholtz.magnetic_local n hn z u) F
  rw [ht] at h1
  have h2 : Integrable (fun x => ∑ i : Fin 3,
      (Packet04WeakSphereMaxwell.permittivity n hn x * electric n hn z T u x i) *
        (η ‖x‖ * dcoord (complexEvaluate p) x i)) := by
    apply integrable_finset_sum
    intro i _
    have hi := WeakAnnularMoment.integrable_mul_compact _ _
      (Packet04TMProjection.displacement_local n hn z T hT u hker i)
      (F i).property.1.continuous (F i).property.2.1
    have hh (x : Space) := congrFun (congrFun ht x) i
    simpa only [hh] using hi
  have h := Packet04TMProjection.actual_magnetic_gradient_test n hn z T hT u hker η hη hc hs p
  rw [ComplexPolarIntegration.integral_polar_complex _ h1,
    ComplexPolarIntegration.integral_polar_complex _ h2] at h
  have hm : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Ioo (0 : ℝ) T →
      magneticCoefficient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        magnetic n hn z u (r • (ω : Space)) j * weight p j ω ∂angularMeasure :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp
      (magneticCoefficient_actual n hn z T u p))
  have hd := displacementGradient_actual n hn z T hT u hker p
  have hleft : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, magnetic n hn z u (r • (ω : Space)) i *
        curl (fun y j => η ‖y‖ * dcoord (complexEvaluate p) y j) (r • (ω : Space)) i
        ∂angularMeasure) =
      -(∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * deriv η r * magneticCoefficient n hn z T u p r) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hm, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    change 0 < r at hr0
    by_cases hrt : r < T
    · rw [hr ⟨hr0, hrt⟩]
      simp only [← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with ω
      have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr0]
      have hx : r • (ω : Space) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact hr0.ne')
      have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
      simp_rw [Packet04RadialCurl.curl_radial_mul_gradient η hη p _ hx, hnorm,
        HarmonicRadiationGeometry.angularToroidal_smul p (l+1) hp]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [weight]
      simp only [pow_succ, pow_add]
      field_simp [hrne]
      ring
    · have hn : r ∉ tsupport η := fun ht => hrt (hs ht).2
      have hz : deriv η r = 0 := by
        simpa only [deriv_zero] using (not_mem_tsupport_iff_eventuallyEq.mp hn).deriv_eq
      simp only [hz, mul_zero, zero_mul, neg_zero]
      rw [← integral_const_mul]
      apply integral_eq_zero_of_ae
      filter_upwards with ω
      have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr0]
      have hx : r • (ω : Space) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact hr0.ne')
      simp [Packet04RadialCurl.curl_radial_mul_gradient η hη p _ hx, hnorm, hz]
  have hright : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, (Packet04WeakSphereMaxwell.permittivity n hn (r • (ω : Space)) *
        electric n hn z T u (r • (ω : Space)) i) *
        (η ‖r • (ω : Space)‖ * dcoord (complexEvaluate p) (r • (ω : Space)) i)
        ∂angularMeasure) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * displacementGradient n hn z T u p r := by
    apply integral_congr_ae
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    change 0 < r at hr0
    rw [hr]
    simp only [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr0]
    have hpd (j : Fin 3) : (MvPolynomial.pderiv j p).IsHomogeneous l := by simpa using hp.pderiv (i := j)
    simp only [hnorm, complexEvaluate_partial,
      FischerDecomposition.complexEvaluate_smul _ l (hpd _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [HarmonicMomentCoupling.gradientWeight, SphericalMomentEquation.angularPolynomial, complexEvaluate]
    rw [FischerDecomposition.evaluate_smul _ l (hpd j)]
    push_cast
    simp only [pow_add]
    ring
  rw [hleft, hright] at h
  linear_combination -h

def electricCoordinates (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (j : Fin 3) : FourierL2.ScalarL2 :=
  NewtonL2.physicalCoordinate (ComplexExteriorResponse.response
    (ModalWeightedMode.coefficient n hn) z 1 T u) j

def electricRadial (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  HarmonicMomentIntegrability.radialMoment (electricCoordinates n hn z T u) p r

def electricGradient (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  HarmonicMomentIntegrability.gradientMoment (electricCoordinates n hn z T u) p r

theorem electricRadial_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      electricRadial n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        electric n hn z T u (r • (ω : Space)) j *
          HarmonicMomentCoupling.radialWeight p j ω ∂angularMeasure := by
  let E := electricCoordinates n hn z T u
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (E j))
  have he := ae_all_iff.mpr (fun j : Fin 3 => PolarMomentAE.polar_ae
    (NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) j))
  filter_upwards [hi, he] with r hr he
  change (∑ j : Fin 3, ∫ ω : Sphere, E j (r • (ω : Space)) *
    HarmonicMomentCoupling.radialWeight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      E j (r • (ω : Space)) * HarmonicMomentCoupling.radialWeight p j ω) angularMeasure :=
    (hr j).integrable_mul (HarmonicMomentCoupling.weight_memLp p j).1
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : ℂ => v * HarmonicMomentCoupling.radialWeight p j ω) (hω j)

theorem electricGradient_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      electricGradient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        electric n hn z T u (r • (ω : Space)) j *
          HarmonicMomentCoupling.gradientWeight p j ω ∂angularMeasure := by
  let E := electricCoordinates n hn z T u
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (E j))
  have he := ae_all_iff.mpr (fun j : Fin 3 => PolarMomentAE.polar_ae
    (NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) j))
  filter_upwards [hi, he] with r hr he
  change (∑ j : Fin 3, ∫ ω : Sphere, E j (r • (ω : Space)) *
    HarmonicMomentCoupling.gradientWeight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      E j (r • (ω : Space)) * HarmonicMomentCoupling.gradientWeight p j ω) angularMeasure :=
    (hr j).integrable_mul (HarmonicMomentCoupling.weight_memLp p j).2
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : ℂ => v * HarmonicMomentCoupling.gradientWeight p j ω) (hω j)

/-- Scalar first-order identity from the actual electric curl equation. -/
theorem electric_toroidal_weak (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (hh : formalLaplacian p = 0) (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) T) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) *
      (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
        (electricGradient n hn z T u p r - (l+1 : ℂ)*electricRadial n hn z T u p r) +
       (l+1 : ℂ)*(l+2 : ℂ)*η r*electricRadial n hn z T u p r)) =
      I*z * ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*η r *
        magneticCoefficient n hn z T u p r := by
  have h := Packet04TMProjection.actual_toroidal_polar n hn z T hT u hker η hη hc hs p l hp hh
  have hE1 := electricRadial_actual n hn z T u p
  have hE2 := electricGradient_actual n hn z T u p
  have hM : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Ioo (0 : ℝ) T →
      magneticCoefficient n hn z T u p r = ∫ ω : Sphere, ∑ j : Fin 3,
        magnetic n hn z u (r • (ω : Space)) j * weight p j ω ∂angularMeasure :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp (magneticCoefficient_actual n hn z T u p))
  let E := electricCoordinates n hn z T u
  have hslices := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (E j))
  have hcoords := ae_all_iff.mpr (fun j : Fin 3 => PolarMomentAE.polar_ae
    (NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) j))
  have hleft : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, electric n hn z T u (r • (ω : Space)) i *
        ((r : ℂ)^l * (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
          DebyeRadialTrace.angularPoloidal p (l+1) (ω : Space) i +
          ((l+1 : ℂ)*(l+2 : ℂ)*η r) * complexEvaluate p (ω : Space) *
            ((ω : Space) i : ℂ))) ∂angularMeasure) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) *
        (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
          (electricGradient n hn z T u p r - (l+1 : ℂ)*electricRadial n hn z T u p r) +
         (l+1 : ℂ)*(l+2 : ℂ)*η r*electricRadial n hn z T u p r) := by
    apply integral_congr_ae
    filter_upwards [hE1,hE2,hslices,hcoords] with r hr1 hr2 hslice hcoord
    rw [hr1, hr2]
    have hIr : Integrable (fun ω : Sphere => ∑ j : Fin 3,
        electric n hn z T u (r • (ω : Space)) j * HarmonicMomentCoupling.radialWeight p j ω) angularMeasure := by
      apply (integrable_finset_sum _ (fun j _ => (hslice j).integrable_mul
        (HarmonicMomentCoupling.weight_memLp p j).1)).congr
      filter_upwards [ae_all_iff.mpr hcoord] with ω hω
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v : ℂ => v * HarmonicMomentCoupling.radialWeight p j ω) (hω j)
    have hIg : Integrable (fun ω : Sphere => ∑ j : Fin 3,
        electric n hn z T u (r • (ω : Space)) j * HarmonicMomentCoupling.gradientWeight p j ω) angularMeasure := by
      apply (integrable_finset_sum _ (fun j _ => (hslice j).integrable_mul
        (HarmonicMomentCoupling.weight_memLp p j).2)).congr
      filter_upwards [ae_all_iff.mpr hcoord] with ω hω
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v : ℂ => v * HarmonicMomentCoupling.gradientWeight p j ω) (hω j)
    let fr := fun ω : Sphere => ∑ j : Fin 3, electric n hn z T u (r • (ω : Space)) j *
      HarmonicMomentCoupling.radialWeight p j ω
    let fg := fun ω : Sphere => ∑ j : Fin 3, electric n hn z T u (r • (ω : Space)) j *
      HarmonicMomentCoupling.gradientWeight p j ω
    let A : ℂ := (r : ℂ)*deriv η r+(l+2 : ℂ)*η r
    let B : ℂ := (l+1 : ℂ)*(l+2 : ℂ)*η r
    have hcomb : A * ((∫ ω, fg ω ∂angularMeasure) - (l+1 : ℂ) *
        (∫ ω, fr ω ∂angularMeasure)) + B * (∫ ω, fr ω ∂angularMeasure) =
        ∫ ω, A * (fg ω - (l+1 : ℂ)*fr ω) + B*fr ω ∂angularMeasure := by
      have hdiff : Integrable (fun ω => fg ω - (l+1 : ℂ)*fr ω) angularMeasure := by
        simpa only [fg, fr, Pi.sub_apply] using hIg.sub (hIr.const_mul (l+1 : ℂ))
      rw [integral_add (hdiff.const_mul A) (hIr.const_mul B),
        integral_const_mul, integral_const_mul, integral_sub hIg (hIr.const_mul (l+1 : ℂ)),
        integral_const_mul]
    change _ = (r : ℂ)^(l+2) * (A * ((∫ ω, fg ω ∂angularMeasure) -
      (l+1 : ℂ) * (∫ ω, fr ω ∂angularMeasure)) + B * (∫ ω, fr ω ∂angularMeasure))
    rw [hcomb, ← integral_const_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    dsimp only [A, B, fg, fr]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hnorm : ‖(ω : Space)‖ = 1 := sphere_norm ω
    simp [DebyeRadialTrace.angularPoloidal, HarmonicMomentCoupling.gradientWeight,
      HarmonicMomentCoupling.radialWeight, SphericalMomentEquation.angularPolynomial,
      complexEvaluate_partial, complexEvaluate, hnorm, pow_add]
    ring
  have hright : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere,
      ∑ i : Fin 3, magnetic n hn z u (r • (ω : Space)) i *
        (η r * (r : ℂ)^(l+1) * DebyeRadialTrace.angularToroidal p (ω : Space) i)
        ∂angularMeasure) = ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*η r *
          magneticCoefficient n hn z T u p r := by
    apply integral_congr_ae
    filter_upwards [hM, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    by_cases hrt : r < T
    · rw [hr ⟨hr0,hrt⟩]
      simp only [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [weight]
      simp only [pow_add]
      ring
    · have hz : η r = 0 := image_eq_zero_of_nmem_tsupport (fun ht => hrt (hs ht).2)
      simp [hz]
  rw [hleft, hright] at h
  exact h

#print axioms OQ14.Packet04TMMoments.electric_toroidal_weak

#print axioms OQ14.Packet04TMMoments.electricRadial_actual
#print axioms OQ14.Packet04TMMoments.electricGradient_actual

#print axioms OQ14.Packet04TMMoments.magnetic_gradient_weak

#print axioms OQ14.Packet04TMMoments.displacementGradient_local
#print axioms OQ14.Packet04TMMoments.displacementGradient_actual

#print axioms OQ14.Packet04TMMoments.magnetic_displacement_coefficient

#print axioms OQ14.Packet04TMMoments.magnetic_displacement_weak

#print axioms OQ14.Packet04TMMoments.displacementRadial_local
#print axioms OQ14.Packet04TMMoments.displacementCoordinates_actual
#print axioms OQ14.Packet04TMMoments.displacementRadial_actual

#print axioms OQ14.Packet04TMMoments.magneticCoefficient_local
#print axioms OQ14.Packet04TMMoments.magneticCoefficient_actual
end OQ14.Packet04TMMoments
