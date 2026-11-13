import Packet05CutoffTangentialArrays
import Packet05NormalFluxContinuity
import Packet05RegionalDivergenceCongruence

/-! Continuous normal flux from local second tangential derivatives of the
actual scalar transmission field and forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05LocalNormalFluxContinuity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalDivergenceCongruence OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05CutoffTangentialArrays OQ14.Packet05NormalFluxContinuity

theorem local_normal_flux_continuous (W V U : Set Space) (hU : IsOpen U) (hUV : U ⊆ V) (hVW : V ⊆ W)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (C F : L2Vector)
    (DC DF : Fin 3 → L2Vector) (HC HF : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn W (fun j => flux A C d hd j-F j) 0)
    (hDC : ∀ i, i ≠ 2 → ∀ j, HasPartialOn W (C j) (DC i j) i)
    (hDF : ∀ i, i ≠ 2 → ∀ j, HasPartialOn W (F j) (DF i j) i)
    (hHC : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn W (DC i j) (HC i t j) t)
    (hHF : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn W (DF i j) (HF i t j) t)
    (θ η χ : Test) (hθ2 : ContDiff ℝ 2 θ.function) (hθW : tsupport θ.function ⊆ W)
    (hθV : ∀ x ∈ V, θ.function x = 1)
    (hηV : tsupport η.function ⊆ V) (hηU : ∀ x ∈ U, η.function x = 1)
    (hχU : tsupport χ.function ⊆ U) (hχ2 : ContDiff ℝ 2 χ.function)
    (T : Set Space) (hT : IsOpen T) (hTU : T ⊆ U) (hχT : ∀ x ∈ T, χ.function x = 1) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] f := by
  let C' : L2Vector := fun j => scaleL2 θ.function θ.regular.continuous θ.compact (C j)
  let F' : L2Vector := fun j => scaleL2 θ.function θ.regular.continuous θ.compact (F j)
  obtain ⟨C1,C2,hC1,hC2⟩ := cutoff_tangential_arrays W θ hθ2 hθW C DC HC hDC hHC
  obtain ⟨F1,F2,hF1,hF2⟩ := cutoff_tangential_arrays W θ hθ2 hθW F DF HF hDF hHF
  have hCeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → C' j x = C j x := by
    filter_upwards [scaleL2_ae θ.function θ.regular.continuous θ.compact (C j)] with x hx hVx
    rw [hx,hθV x hVx,one_mul]
  have hFeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → F' j x = F j x := by
    filter_upwards [scaleL2_ae θ.function θ.regular.continuous θ.compact (F j)] with x hx hVx
    rw [hx,hθV x hVx,one_mul]
  have hdivV : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0 :=
    fun φ hφ => hdiv φ (hφ.trans hVW)
  have hdiv' : HasDivergenceOn V (fun j => flux A C' d hd j-F' j) 0 := by
    apply divergence_on_of_ae_eq V _ _ 0 hdivV
    intro j
    filter_upwards [flux_local_ae_eq V A C C' d hd hCeq j,hFeq j,
      Lp.coeFn_sub (flux A C' d hd j) (F' j),Lp.coeFn_sub (flux A C d hd j) (F j)] with x ha hb hc hd' hx
    rw [hc,hd']
    simp only [Pi.sub_apply,ha hx,hb hx]
  obtain ⟨f,hfc,hfe⟩ := normal_flux_continuous V U hU hUV A hA2 hA3 C' F' C1 F1 C2 F2 d hd hdiv'
    hC1 hF1 hC2 hF2 η χ hηV hηU hχU hχ2
  refine ⟨f,hfc,?_⟩
  have hp : ∀ᵐ x ∂volume, x ∈ V → (flux A C' d hd 2-F' 2 : L2Scalar) x =
      (flux A C d hd 2-F 2 : L2Scalar) x := by
    filter_upwards [flux_local_ae_eq V A C C' d hd hCeq 2,hFeq 2,
      Lp.coeFn_sub (flux A C' d hd 2) (F' 2),Lp.coeFn_sub (flux A C d hd 2) (F 2)] with x ha hb hc hd' hx
    rw [hc,hd']
    simp only [Pi.sub_apply,ha hx,hb hx]
  apply (ae_restrict_iff' hT.measurableSet).mpr
  filter_upwards [hfe, hp,
    scaleL2_ae χ.function χ.regular.continuous χ.compact
      (scaleL2 η.function η.regular.continuous η.compact (flux A C' d hd 2-F' 2)),
    scaleL2_ae η.function η.regular.continuous η.compact (flux A C' d hd 2-F' 2)] with x ha hb hc hd' hx
  have hxU := hTU hx
  have hxV := hUV hxU
  rw [hc,hd',hχT x hx,hηU x hxU,one_mul,one_mul,hb hxV] at ha
  exact ha

end OQ14.Packet05LocalNormalFluxContinuity
#print axioms OQ14.Packet05LocalNormalFluxContinuity.local_normal_flux_continuous
