import Packet04ElectricToroidal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04ToroidalMoments
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.Packet04ElectricToroidal OQ14.DebyeCalculus OQ14.DebyeRadialTrace
  OQ14.Packet04VectorTests OQ14.AngularPower OQ14.HarmonicPolynomial
  OQ14.PolarMomentTesting OQ14.PolarMomentEnergy OQ14.SphericalMomentEquation
  OQ14.ComplexSphereMaxwell OQ14.ModalWeightedMode OQ14.ModalMeridionalReflection

def weight (p : Poly) (j : Fin 3) (ω : Sphere) : ℂ := angularToroidal p (ω : Space) j

theorem weight_continuous (p : Poly) (j : Fin 3) : Continuous (weight p j) :=
  ((continuous_apply j).comp (HarmonicRadiationGeometry.angularToroidal_continuous p)).comp
    continuous_subtype_val

theorem weight_memLp (p : Poly) (j : Fin 3) : MemLp (weight p j) 2 angularMeasure :=
  (weight_continuous p j).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def coefficient (V : VectorFourier.VectorL2) (p : Poly) (r : ℝ) : ℂ :=
  ∑ j : Fin 3, moment (NewtonL2.physicalCoordinate V j) (weight p j) r

theorem coefficient_local (V : VectorFourier.VectorL2) (p : Poly) :
    LocallyIntegrableOn (coefficient V p) (Ioi (0 : ℝ)) := by
  have hi (j : Fin 3) := Packet01MomentIntegrability.moment_locallyIntegrableOn
    (NewtonL2.physicalCoordinate V j) (weight p j)
    (weight_continuous p j).measurable (weight_memLp p j)
  have he : coefficient V p = (fun r =>
      moment (NewtonL2.physicalCoordinate V 0) (weight p 0) r +
      moment (NewtonL2.physicalCoordinate V 1) (weight p 1) r +
      moment (NewtonL2.physicalCoordinate V 2) (weight p 2) r) := by
    ext r; simp [coefficient, Fin.sum_univ_three]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem coefficient_actual (V : VectorFourier.VectorL2) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      coefficient V p r = ∫ ω : Sphere, ∑ j : Fin 3,
        V (VectorFourier.coordinateMap (r • (ω : Space))) j * weight p j ω ∂angularMeasure := by
  have hi := ae_all_iff.mpr (fun j : Fin 3 => slice_memLp_ae (NewtonL2.physicalCoordinate V j))
  have he := ae_all_iff.mpr (fun j : Fin 3 =>
    PolarMomentAE.polar_ae (NewtonL2.physicalCoordinate_ae V j))
  filter_upwards [hi, he] with r hr he
  change (∑ j : Fin 3, ∫ ω : Sphere,
    NewtonL2.physicalCoordinate V j (r • (ω : Space)) * weight p j ω ∂angularMeasure) = _
  have hint (j : Fin 3) : Integrable (fun ω : Sphere =>
      NewtonL2.physicalCoordinate V j (r • (ω : Space)) * weight p j ω) angularMeasure :=
    (hr j).integrable_mul (weight_memLp p j)
  rw [← integral_finset_sum Finset.univ (fun j _ => hint j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply Finset.sum_congr rfl
  intro j _
  rw [hω j]

theorem actual_weighted_annihilation
    (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) T) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r *
      coefficient (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) p r) = 0 := by
  let V := ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.false
  have hφ := test_regular η hη h0 p
  have hφc := test_compact η hc p
  have hφs : tsupport (test η p) ⊆ ball (0 : Space) T := by
    intro x hx
    have hh := RadialNormTest.radialNorm_tsupport η (tsupport_mul_subset_left hx)
    simpa [Metric.mem_ball, dist_zero_right] using (hs hh).2
  have h := actual_test_annihilation n hn z T hT u hu hker (test η p) hφ hφc hφs
  have hi := vector_integrable (ball (0 : Space) T) (electric n hn z T u)
    (Packet04WeakSphereMaxwell.electric_local n hn z T u)
    (radialTest _ (test η p) hφ hφc hφs)
  change Integrable (fun x => ∑ j : Fin 3,
    electric n hn z T u x j * toroidal (test η p) x j) at hi
  rw [ComplexPolarIntegration.integral_polar_complex _ hi] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [coefficient_actual V p, ae_restrict_mem measurableSet_Ioi] with r hc hr
  have hsphere : (∫ ω : Sphere, ∑ j : Fin 3,
      electric n hn z T u (r • (ω : Space)) j *
        toroidal (test η p) (r • (ω : Space)) j ∂angularMeasure) =
      (η r * (r : ℂ)^l) * coefficient V p r := by
    rw [hc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change _ * curl (radialVector (test η p)) _ _ = _
    rw [Packet04RadialCurl.radial_test_curl_on_ray η hη p l hp r hr ω j]
    change V _ j * (η r * (r : ℂ)^l * weight p j ω) = _
    ring
  rw [hsphere, pow_add]
  ring

theorem actual_coefficient_zero
    (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) T),
      coefficient (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) p r = 0 := by
  let V := ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
  let g := fun r : ℝ => (r : ℂ)^(l+2) * coefficient V p r
  have hg : LocallyIntegrableOn g (Ioo (0 : ℝ) T) :=
    ((coefficient_local V p).continuousOn_mul
      (Complex.continuous_ofReal.pow (l+2)).continuousOn isOpen_Ioi.isLocallyClosed).mono_set
        (fun _ hr => hr.1)
  have ha : ∀ᵐ r : ℝ, r ∈ Ioo (0 : ℝ) T → g r = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hg (by
      intro η hη hc hs
      have hηc : ContDiff ℝ (⊤ : ℕ∞) (fun r => (η r : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hη
      have hcc : HasCompactSupport (fun r => (η r : ℂ)) :=
        hc.comp_left (by simp : Complex.ofReal 0 = 0)
      have hsc : tsupport (fun r => (η r : ℂ)) ⊆ Ioo (0 : ℝ) T := by
        have he : tsupport (fun r => (η r : ℂ)) = tsupport η := by
          apply congrArg closure; ext r; exact not_congr Complex.ofReal_eq_zero
        rwa [he]
      have hw := actual_weighted_annihilation n hn z T hT u hu hker p l hp
        (fun r => (η r : ℂ)) hηc hcc hsc
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hw
      · convert hw using 1
        apply integral_congr_ae
        filter_upwards with r
        simp only [Complex.real_smul, g, V]
        ring
      · intro r hr
        have hz : η r = 0 := image_eq_zero_of_nmem_tsupport (fun ht => hr (hs ht).1)
        simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul])
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr ha,
    ae_restrict_mem measurableSet_Ioo] with r hr hri
  exact (mul_eq_zero.mp hr).resolve_left
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hri.1.ne'))

theorem actual_toroidal_zero
    (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) T),
      (∫ ω : Sphere, ∑ j : Fin 3,
        electric n hn z T u (r • (ω : Space)) j *
          angularToroidal p (ω : Space) j ∂angularMeasure) = 0 := by
  have hb := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
    (coefficient_actual (ComplexExteriorResponse.response
      (ModalWeightedMode.coefficient n hn) z 1 T u) p)
  filter_upwards [actual_coefficient_zero n hn z T hT u hu hker p l hp, hb] with r hz hb
  exact hb.symm.trans hz

end OQ14.Packet04ToroidalMoments
#print axioms OQ14.Packet04ToroidalMoments.weight_continuous
#print axioms OQ14.Packet04ToroidalMoments.weight_memLp
#print axioms OQ14.Packet04ToroidalMoments.coefficient_local
#print axioms OQ14.Packet04ToroidalMoments.coefficient_actual
#print axioms OQ14.Packet04ToroidalMoments.actual_weighted_annihilation
#print axioms OQ14.Packet04ToroidalMoments.actual_coefficient_zero
#print axioms OQ14.Packet04ToroidalMoments.actual_toroidal_zero
