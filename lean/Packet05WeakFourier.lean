import Packet05AnisotropicEmbedding
import WeakPoynting.PartialSmoothing
import NewtonHessian
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import WeakPoynting.Compactness
import Packet05LocalDerivative

/-! The Fourier multiplier identity for a genuine weak L² partial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05WeakFourier
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.PartialSmoothing
open scoped Topology SchwartzMap FourierTransform

theorem weak_partial_compact {u D : L2Scalar} (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) : CompactRepresentative D := by
  obtain ⟨f, hf, huf⟩ := hu
  let K := tsupport f
  have hK : IsCompact K := hf.isCompact
  have hV : IsOpen Kᶜ := isClosed_closure.isOpen_compl
  have hu0 : ∀ᵐ x ∂volume, x ∈ Kᶜ → u x = (1 : ℂ) * (0 : L2Scalar) x := by
    filter_upwards [huf, Lp.coeFn_zero ℂ (2 : ENNReal) (volume : Measure Space)] with x hx hz hmem
    have hfzero : f x = 0 := image_eq_zero_of_nmem_tsupport hmem
    rw [hz, hx, hfzero]
    simp
  have hzero : HasWeakPartial (0 : L2Scalar) 0 i := by
    intro φ
    simp
  have hDzero := Packet05LocalDerivative.weak_partial_local_constant_relation Kᶜ hV
    0 u 0 D 1 i hzero hD hu0
  apply WeakCompactness.supported_compact hK
  filter_upwards [hDzero, Lp.coeFn_zero ℂ (2 : ENNReal) (volume : Measure Space)] with x hx hz hnot
  have hh := hx hnot
  rw [hz] at hh
  simpa using hh

theorem inverse_fourier_weak_partial {u D : L2Scalar} (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) :
    ∀ᵐ ξ : Space ∂volume,
      FourierL2.fourierEquiv.symm D ξ =
        -(2 * Real.pi * Complex.I) * (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ := by
  let U := FourierL2.fourierEquiv.symm u
  let V := FourierL2.fourierEquiv.symm D
  let c : ℂ := -(2 * Real.pi * Complex.I)
  have hl : LocallyIntegrable (fun ξ : Space => V ξ - c * (ξ i : ℂ) * U ξ) := by
    apply ((Lp.memLp V).locallyIntegrable (by norm_num)).sub
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply IntegrableOn.continuousOn_mul
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous)).continuousOn
    · exact ((Lp.memLp U).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
    · exact hK
  have hz : ∀ᵐ ξ : Space ∂volume, V ξ - c * (ξ i : ℂ) * U ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hl
    intro ρ hρ hρc
    let R : Space → ℂ := fun ξ => (ρ ξ : ℂ)
    let S : Space → ℂ := fun ξ => c * (ξ i : ℂ) * R ξ
    have hR : Continuous R := Complex.continuous_ofReal.comp hρ.continuous
    have hRc : HasCompactSupport R := hρc.comp_left Complex.ofRealCLM.map_zero
    have hS : Continuous S := (continuous_const.mul (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj i).continuous)).mul hR
    have hSc : HasCompactSupport S := hRc.mul_left
    let un : ℕ → 𝓢(Space, ℂ) := fun n => smoothSchwartz (shrinkingBump n) u hu
    have huconv : Tendsto (fun n => FourierL2.embed (un n)) atTop (𝓝 u) := by
      simp only [un, embed_smoothSchwartz]
      exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto u
    have hdconv : Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (un n))) atTop (𝓝 D) := by
      simp only [un, embed_partial_smoothSchwartz _ hu hD]
      exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto D
    have hUconv := FourierL2.fourierEquiv.symm.continuous.tendsto u |>.comp huconv
    have hVconv := FourierL2.fourierEquiv.symm.continuous.tendsto D |>.comp hdconv
    have hlim := ((testPair R hR hRc).continuous.tendsto _ |>.comp hVconv).sub
      ((testPair S hS hSc).continuous.tendsto _ |>.comp hUconv)
    have hseq (n : ℕ) :
        testPair R hR hRc (FourierL2.fourierEquiv.symm
          (FourierL2.embed (GradientProjection.pderivative i (un n)))) -
        testPair S hS hSc (FourierL2.fourierEquiv.symm (FourierL2.embed (un n))) = 0 := by
      rw [FourierL2.fourierEquiv_symm_embed, FourierL2.fourierEquiv_symm_embed,
        testPair_integral, testPair_integral, ← integral_sub]
      · apply integral_eq_zero_of_ae
        filter_upwards [FourierL2.embed_ae ((SchwartzMap.fourierTransformCLE ℂ).symm
            (GradientProjection.pderivative i (un n))),
          FourierL2.embed_ae ((SchwartzMap.fourierTransformCLE ℂ).symm (un n))] with ξ hv hu'
        change (FourierL2.embed ((SchwartzMap.fourierTransformCLE ℂ).symm
          (GradientProjection.pderivative i (un n))) ξ * R ξ -
          FourierL2.embed ((SchwartzMap.fourierTransformCLE ℂ).symm (un n)) ξ * S ξ) = 0
        rw [hv, hu', NewtonHessian.inverse_fourier_pderivative]
        simp only [S, c]
        ring
      · exact testPair_integrable R hR hRc _
      · exact testPair_integrable S hS hSc _
    have heq := tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hseq n).symm)))
    rw [testPair_integral, testPair_integral, ← integral_sub
      (testPair_integrable R hR hRc V) (testPair_integrable S hS hSc U)] at heq
    convert heq using 1
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [Pi.sub_apply, R, S, Complex.real_smul]
    ring
  filter_upwards [hz] with ξ hξ
  exact sub_eq_zero.mp hξ

theorem frequency_coordinate_memLp {u D : L2Scalar} (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) :
    MemLp (fun ξ : Space => (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ) 2 volume := by
  let c : ℂ := -(2 * Real.pi * Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have h := (Lp.memLp (FourierL2.fourierEquiv.symm D)).const_mul c⁻¹
  apply MemLp.ae_eq ?_ h
  filter_upwards [inverse_fourier_weak_partial hu i hD] with ξ hξ
  change c⁻¹ * FourierL2.fourierEquiv.symm D ξ = _
  rw [hξ]
  change c⁻¹ * (c * (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ) = _
  field_simp
  ring

theorem frequency_mixed_memLp {u D H : L2Scalar} (hu : CompactRepresentative u)
    (i j : Fin 3) (hD : HasWeakPartial u D i) (hH : HasWeakPartial D H j) :
    MemLp (fun ξ : Space => (ξ i : ℂ) * (ξ j : ℂ) * FourierL2.fourierEquiv.symm u ξ) 2 volume := by
  let c : ℂ := -(2 * Real.pi * Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hDc := weak_partial_compact hu i hD
  have hm := (frequency_coordinate_memLp hDc j hH).const_mul c⁻¹
  apply MemLp.ae_eq ?_ hm
  filter_upwards [inverse_fourier_weak_partial hu i hD] with ξ hξ
  change c⁻¹ * ((ξ j : ℂ) * FourierL2.fourierEquiv.symm D ξ) = _
  rw [hξ]
  change c⁻¹ * ((ξ j : ℂ) * (c * (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ)) = _
  field_simp
  ring

end OQ14.Packet05WeakFourier
#print axioms OQ14.Packet05WeakFourier.inverse_fourier_weak_partial
#print axioms OQ14.Packet05WeakFourier.weak_partial_compact
#print axioms OQ14.Packet05WeakFourier.frequency_coordinate_memLp
#print axioms OQ14.Packet05WeakFourier.frequency_mixed_memLp
