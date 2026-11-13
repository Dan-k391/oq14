import Packet04TMClassical
import ComplexKernelDebye
import Packet04RaisingPhysical
import Packet04TMMatching

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04TMProfiles
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments
open scoped Topology

theorem electricRadial_inner (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2) (p : Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      electricRadial n hn z T u p r = ComplexKernelDebye.radialCoefficient n hn z u p r := by
  have ho : ∀ᵐ x : Space ∂volume, x ∈ closedBall 0 1 → ∀ j : Fin 3,
      ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u
        (VectorFourier.coordinateMap x) j = ComplexSphereMaxwell.electric n hn z T u x j := by
    have h := (ae_restrict_iff' measurableSet_closedBall).mp (ae_all_iff.mpr (fun j =>
      ComplexResponseOverlap.response_overlap (ModalWeightedMode.coefficient n hn) z 1 1 T hT u
        (ModalWeightedMode.coefficient_support n hn) j))
    filter_upwards [h] with x hx hball j
    have hj := hx hball j
    change ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 1 u
      (VectorFourier.coordinateMap x) j = _ at hj
    simpa [ComplexSphereMaxwell.electric, ComplexExteriorResponse.response,
      ComplexKernelResponse.response, show (1 : ℝ) + 1 = 2 by norm_num] using hj
  have hp := PolarMomentAE.polar_ae ho
  have he := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
    (electricRadial_actual n hn z T u p)
  have hp' := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1) hp
  filter_upwards [he,hp',ae_restrict_mem measurableSet_Ioo] with r he hp hr
  rw [he]
  unfold ComplexKernelDebye.radialCoefficient
  apply integral_congr_ae
  filter_upwards [hp] with ω hω
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr.1]
  have hball : r • (ω : Space) ∈ closedBall (0 : Space) 1 := by
    simpa [mem_closedBall, dist_zero_right, hnorm] using hr.2.le
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hω hball j]
  simp [HarmonicMomentCoupling.radialWeight]
  ring

/-- The genuine exterior TM representative is purely outgoing. -/
theorem actual_exterior_outgoing (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (U V : ℝ → ℂ) (hUc : ContinuousOn U (Ioo (0 : ℝ) T)) (hVc : ContinuousOn V (Ioo (0 : ℝ) T))
    (hU : (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] U)
    (hV : (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] V)
    (hUi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → U d-U c =
      ∫ r in c..d, (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r)
    (hVi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → V d-V c =
      ∫ r in c..d, (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
        z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) :
    ∃ b : ℂ, ∀ r ∈ Ioo (1 : ℝ) T,
      U r = b * RadialRellich.outgoing (l+1) z r ∧
      V r = b * RadialRellich.outgoingD (l+1) z r := by
  let lam : ℂ := (l+1 : ℂ)*(l+2 : ℂ)
  have hlam : lam ≠ 0 := mul_ne_zero (by exact_mod_cast (show l+1 ≠ 0 by omega))
    (by exact_mod_cast (show l+2 ≠ 0 by omega))
  have hsub : Ioo (1 : ℝ) T ⊆ Ioo (0 : ℝ) T := fun _ hr => ⟨by linarith [hr.1],hr.2⟩
  have hs := Packet04TMClassical.region_ode n hn z T hT.le u hker p l (Ioo 1 T)
    isOpen_Ioo hsub 1 one_ne_zero (by intro r hr; simp [Packet04TMDielectric.radialPermittivity, not_lt_of_ge hr.1.le])
    U V hUc hVc hU hV hUi hVi
  have hf (r : ℝ) (hr : r ∈ Ioo 1 T) : HasDerivAt (fun r => U r / lam) (V r / lam) r := by
    simpa using (hs.1 r hr).div_const lam
  have hdf (r : ℝ) (hr : r ∈ Ioo 1 T) : HasDerivAt (fun r => V r / lam)
      (RadialRellich.radialCoefficient (l+1) z r * (U r / lam)) r := by
    convert (hs.2 r hr).div_const lam using 1
    dsimp [RadialRellich.radialCoefficient, lam]
    push_cast
    ring
  have hactual : ∀ᵐ r : ℝ ∂volume.restrict (Ioo 1 T),
      ((r : ℂ)^2 * radialMoment (electricCoordinates n hn z T u) p r = lam*(U r/lam)) ∧
      ((r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r = lam*(V r/lam)) := by
    have hUa := ae_restrict_of_ae_restrict_of_subset hsub hU
    have hVa := ae_restrict_of_ae_restrict_of_subset hsub hV
    have hDa := ae_restrict_of_ae_restrict_of_subset
      (show Ioo (1 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => lt_trans (by norm_num) hr.1)
      (Packet04TMDielectric.displacement_radial_factor n hn z T hT.le u hker p)
    filter_upwards [hUa,hVa,hDa,ae_restrict_mem measurableSet_Ioo] with r hu hv hd hr
    have he : Packet04TMDielectric.radialPermittivity n r = 1 := by
      simp [Packet04TMDielectric.radialPermittivity, not_lt_of_ge hr.1.le]
    rw [he, one_mul] at hd
    change (r : ℂ)^2 * electricRadial n hn z T u p r = _ ∧ _
    rw [hd] at hu
    constructor <;> field_simp [hlam] <;> assumption
  obtain ⟨c,hc⟩ := Packet04RaisingPhysical.actual_TM_outgoing n hn z hz T hT u p l hp hh
    (fun r => U r/lam) (fun r => V r/lam) hf hdf hactual
  refine ⟨lam*c, ?_⟩
  intro r hr
  have hUr : U r = (lam*c)*RadialRellich.outgoing (l+1) z r := by
    have h := hc r hr
    field_simp [hlam] at h
    linear_combination h
  have hder : HasDerivAt (fun r => U r/lam) (c * RadialRellich.outgoingD (l+1) z r) r := by
    have heq : (fun r => U r/lam) =ᶠ[𝓝 r] fun r => c*RadialRellich.outgoing (l+1) z r :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun _ hs => hc _ hs)
    exact ((RadialRellich.outgoing_hasDerivAt (l+1) z hz r (ne_of_gt (lt_trans (by norm_num) hr.1))).const_mul c).congr_of_eventuallyEq heq
  have hv := (hf r hr).unique hder
  constructor
  · exact hUr
  · field_simp [hlam] at hv
    linear_combination hv

/-- The genuine interior TM representative is the regular radial solution. -/
theorem actual_interior_regular (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (U V : ℝ → ℂ) (hUc : ContinuousOn U (Ioo (0 : ℝ) T)) (hVc : ContinuousOn V (Ioo (0 : ℝ) T))
    (hU : (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] U)
    (hV : (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] V)
    (hUi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → U d-U c =
      ∫ r in c..d, (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r)
    (hVi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → V d-V c =
      ∫ r in c..d, (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
        z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) :
    ∃ a : ℂ, ∀ r ∈ Ioo (0 : ℝ) 1,
      U r = a * RadialOriginSelection.regular (l+1) (z*n) r ∧
      V r = (a/(n : ℂ)^2) * RadialOriginSelection.regularD (l+1) (z*n) r := by
  have hn0 : (n : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by linarith))
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) T := fun _ hr => ⟨hr.1, lt_trans hr.2 hT⟩
  have hs := Packet04TMClassical.region_ode n hn z T hT.le u hker p l (Ioo 0 1)
    isOpen_Ioo hsub ((n : ℂ)^2) hn0
    (by intro r hr; simp [Packet04TMDielectric.radialPermittivity, hr.2])
    U V hUc hVc hU hV hUi hVi
  obtain ⟨c,hc⟩ := ComplexKernelDebye.regular_radial_coefficient n hn z hz u hker p (l+1) hp hh
  have hUi' := ae_restrict_of_ae_restrict_of_subset hsub hU
  have hDi := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
    (Packet04TMDielectric.displacement_radial_factor n hn z T hT.le u hker p)
  have hEi := electricRadial_inner n hn z T hT.le u p
  have hae : U =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r => ((n : ℂ)^2*c)*RadialOriginSelection.regular (l+1) (z*n) r := by
    filter_upwards [hUi',hDi,hEi,hc,ae_restrict_mem measurableSet_Ioo] with r hu hd he hc hr
    have hep : Packet04TMDielectric.radialPermittivity n r = (n : ℂ)^2 := by
      simp [Packet04TMDielectric.radialPermittivity, hr.2]
    rw [hep, he] at hd
    rw [← hu, hd]
    linear_combination (n : ℂ)^2*hc
  have hreg : ContinuousOn (fun r => ((n : ℂ)^2*c)*RadialOriginSelection.regular (l+1) (z*n) r)
      (Ioo (0 : ℝ) 1) := by
    intro r hr
    exact ((RadialOriginSelection.regular_hasDerivAt (l+1) (z*n) r).const_mul _).continuousAt.continuousWithinAt
  have hpoint : EqOn U (fun r => ((n : ℂ)^2*c)*RadialOriginSelection.regular (l+1) (z*n) r)
      (Ioo (0 : ℝ) 1) := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (hUc.mono hsub) hreg
  refine ⟨(n : ℂ)^2*c, ?_⟩
  intro r hr
  have hder : HasDerivAt U (((n : ℂ)^2*c)*RadialOriginSelection.regularD (l+1) (z*n) r) r := by
    have heq : U =ᶠ[𝓝 r] fun r => ((n : ℂ)^2*c)*RadialOriginSelection.regular (l+1) (z*n) r :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun _ hs => hpoint hs)
    exact ((RadialOriginSelection.regular_hasDerivAt (l+1) (z*n) r).const_mul _).congr_of_eventuallyEq heq
  have hv := (hs.1 r hr).unique hder
  constructor
  · exact hpoint hr
  · have hv' : V r = c*RadialOriginSelection.regularD (l+1) (z*n) r :=
      (mul_left_cancel₀ hn0) (by simpa only [mul_assoc] using hv)
    rw [hv']
    field_simp [hn0]

private theorem trace_from_interval (f g : ℝ → ℂ) (a b x : ℝ) (hab : a < b)
    (hx : x ∈ Icc a b) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (he : EqOn f g (Ioo a b)) : f x = g x := by
  have hx' : x ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hx
  have hbot : (𝓝[Ioo a b] x).NeBot := mem_closure_iff_clusterPt.mp hx'
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds) (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- The actual interface traces satisfy the literal named TM matching matrix. -/
theorem actual_matching_traces (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (U V : ℝ → ℂ) (hUc : ContinuousOn U (Ioo (0 : ℝ) T)) (hVc : ContinuousOn V (Ioo (0 : ℝ) T))
    (hU : (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] U)
    (hV : (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r) =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] V)
    (hUi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → U d-U c =
      ∫ r in c..d, (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r)
    (hVi : ∀ c d, uIcc c d ⊆ Ioo (0 : ℝ) T → V d-V c =
      ∫ r in c..d, (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
        z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) :
    ∃ a b : ℂ,
      (∀ r ∈ Ioo (0 : ℝ) 1, U r = a * RadialOriginSelection.regular (l+1) (z*n) r) ∧
      a*ModalAlgebra.psi (l+1) ((n : ℂ)*z)=b*ModalAlgebra.xi (l+1) z ∧
      a*(z/(n : ℂ))*ModalAlgebra.psiD (l+1) ((n : ℂ)*z)=b*z*ModalAlgebra.xiD (l+1) z := by
  obtain ⟨a,ha⟩ := actual_interior_regular n hn z hz T hT u hker p l hp hh U V hUc hVc hU hV hUi hVi
  obtain ⟨b,hb⟩ := actual_exterior_outgoing n hn z hz T hT u hker p l hp hh U V hUc hVc hU hV hUi hVi
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hzn : z*(n : ℂ) ≠ 0 := mul_ne_zero hz hn0
  have h1 : (1 : ℝ) ∈ Ioo 0 T := ⟨by norm_num,hT⟩
  have hUc1 := hUc.continuousAt (isOpen_Ioo.mem_nhds h1)
  have hVc1 := hVc.continuousAt (isOpen_Ioo.mem_nhds h1)
  have hleftU : U 1 = a * RadialOriginSelection.regular (l+1) (z*n) 1 :=
    trace_from_interval U _ 0 1 1 (by norm_num) (by simp) hUc1
      (((RadialOriginSelection.regular_hasDerivAt (l+1) (z*n) 1).const_mul a).continuousAt)
      (fun r hr => (ha r hr).1)
  have hleftV : V 1 = (a/(n : ℂ)^2) * RadialOriginSelection.regularD (l+1) (z*n) 1 :=
    trace_from_interval V _ 0 1 1 (by norm_num) (by simp) hVc1
      (((RadialOriginSelection.regularD_hasDerivAt (l+1) (z*n) hzn 1 (by norm_num)).const_mul _).continuousAt)
      (fun r hr => (ha r hr).2)
  have hrightU : U 1 = b * RadialRellich.outgoing (l+1) z 1 :=
    trace_from_interval U _ 1 T 1 hT (by simp [hT.le]) hUc1
      (((RadialRellich.outgoing_hasDerivAt (l+1) z hz 1 (by norm_num)).const_mul _).continuousAt)
      (fun r hr => (hb r hr).1)
  have hrightV : V 1 = b * RadialRellich.outgoingD (l+1) z 1 :=
    trace_from_interval V _ 1 T 1 hT (by simp [hT.le]) hVc1
      (((RadialRellich.outgoingD_hasDerivAt (l+1) z hz 1 (by norm_num)).const_mul _).continuousAt)
      (fun r hr => (hb r hr).2)
  have hψ : RadialOriginSelection.regular (l+1) (z*n) 1 = ModalAlgebra.psi (l+1) ((n : ℂ)*z) := by
    simp only [RadialOriginSelection.regular, Complex.ofReal_one, mul_one]
    rw [RiccatiOriginSeries.origin_eq_psi _ _ hzn, mul_comm]
  have hψd : RadialOriginSelection.regularD (l+1) (z*n) 1 = (z*n)*ModalAlgebra.psiD (l+1) ((n : ℂ)*z) := by
    simp only [RadialOriginSelection.regularD, Complex.ofReal_one, mul_one]
    rw [RiccatiOriginSeries.originD_eq_psiD _ _ hzn, mul_comm z]
  refine ⟨a,b,fun r hr => (ha r hr).1, ?_, ?_⟩
  · rw [hψ] at hleftU
    simpa [RadialRellich.outgoing] using hleftU.symm.trans hrightU
  · rw [hψd] at hleftV
    have hv := hleftV.symm.trans hrightV
    dsimp [RadialRellich.outgoingD] at hv
    field_simp [hn0] at hv ⊢
    apply mul_left_cancel₀ hn0
    linear_combination hv

/-- All positive physical degrees except the selected dipole have zero actual
interior radial coefficient for a sector-independent sphere kernel vector. -/
theorem actual_nondipole_radial_zero (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hroot : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (hl : l+1 ≠ 1) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u p r = 0 := by
  obtain ⟨U,V,hUc,hVc,hU,hV,hUi,hVi⟩ :=
    Packet04TMGlobalTraces.actual_global_representatives n hn z hz 2 (by norm_num) u hker p l hp hh
  obtain ⟨a,b,ha,hmatch1,hmatch2⟩ :=
    actual_matching_traces n hn z hz 2 (by norm_num) u hker p l hp hh U V hUc hVc hU hV hUi hVi
  have hab := Packet04TMMatching.non_dipole_amplitudes_zero n hn hna z hz hroot (l+1) hl a b hmatch1 hmatch2
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) 2 := fun _ hr => ⟨hr.1, by linarith [hr.2]⟩
  have hu := ae_restrict_of_ae_restrict_of_subset hsub hU
  have hd := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
    (Packet04TMDielectric.displacement_radial_factor n hn z 2 (by norm_num) u hker p)
  have he := electricRadial_inner n hn z 2 (by norm_num) u p
  filter_upwards [hu,hd,he,ae_restrict_mem measurableSet_Ioo] with r hu hd he hr
  have hep : Packet04TMDielectric.radialPermittivity n r = (n : ℂ)^2 := by
    simp [Packet04TMDielectric.radialPermittivity, hr.2]
  have hzero : U r = 0 := by rw [ha r hr, hab.1, zero_mul]
  rw [hzero] at hu
  rw [hep,he] at hd
  have hn0 : (n : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by linarith))
  have hr0 : (r : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.1.ne')
  apply (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero hr0 hn0)
  linear_combination hu - (r : ℂ)^2*hd

#print axioms OQ14.Packet04TMProfiles.actual_nondipole_radial_zero

#print axioms OQ14.Packet04TMProfiles.actual_matching_traces

#print axioms OQ14.Packet04TMProfiles.actual_interior_regular

#print axioms OQ14.Packet04TMProfiles.actual_exterior_outgoing

#print axioms OQ14.Packet04TMProfiles.electricRadial_inner
end OQ14.Packet04TMProfiles
