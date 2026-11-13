import Packet05LocalizedNormalFluxBound
import Packet05PairedArrayCeiling
import Packet05TangentialAssemblyCeiling
import Packet05NormalFluxUniformCeiling

/-! A single fixed normal-flux ceiling from the aligned regional scalar
iteration and the bounded global bootstrapped forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet05RegionalNormalFluxUniform
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05ScalarDielectricFlux
  Packet05QuantitativeLocalArrays Packet05PlateauGraphFlux Packet05AssembleTangentialArrays
  Packet05TangentialAssemblyCeiling Packet05PairedArrayCeiling MaxwellCutoffCommutator Packet05MatrixWeakDerivative

theorem regional_normal_flux_uniform (Vlocal Vreg Wreg T : Set Space)
    (hWreg : IsOpen Wreg) (hWV : Wreg ⊆ Vreg) (hT : IsOpen T) (hTW : T ⊆ Wreg)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn Vreg (fun j => flux A C d hd j-F j) 0)
    (D0 D1 H00 H01 H10 H11 : L2Vector)
    (hD0 : ∀ j, HasPartialOn Vlocal (C j) (D0 j) 0) (hD1 : ∀ j, HasPartialOn Vlocal (C j) (D1 j) 1)
    (hH00 : ∀ j, HasPartialOn Vlocal (D0 j) (H00 j) 0) (hH01 : ∀ j, HasPartialOn Vlocal (D0 j) (H01 j) 1)
    (hH10 : ∀ j, HasPartialOn Vlocal (D1 j) (H10 j) 0) (hH11 : ∀ j, HasPartialOn Vlocal (D1 j) (H11 j) 1)
    (F1 : Fin 3 → L2Vector) (F2 : Fin 3 → Fin 3 → L2Vector)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (K P Q : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hC : ∀ j, ‖C j‖ ≤ K) (hF : ∀ j, ‖F j‖ ≤ K)
    (hD0n : ∀ j, ‖D0 j‖ ≤ P) (hD1n : ∀ j, ‖D1 j‖ ≤ P)
    (hH00n : ∀ j, ‖H00 j‖ ≤ Q) (hH01n : ∀ j, ‖H01 j‖ ≤ Q)
    (hH10n : ∀ j, ‖H10 j‖ ≤ Q) (hH11n : ∀ j, ‖H11 j‖ ≤ Q)
    (hF1n : ∀ i, i ≠ 2 → ∀ j, ‖F1 i j‖ ≤ K)
    (hF2n : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, ‖F2 i t j‖ ≤ K)
    (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function) (hθlocal : tsupport θ.function ⊆ Vlocal)
    (hθV : ∀ x ∈ Vreg, θ.function x = 1)
    (aθ bθ cθ : ℝ) (haθ : ∀ x, ‖θ.function x‖ ≤ aθ) (hbθ : ∀ i x, ‖dcoord θ.function x i‖ ≤ bθ)
    (hcθ : ∀ i j x, ‖dcoord (derivativeCutoff θ hθ2 i).function x j‖ ≤ cθ)
    (η ξ : Test) (hηV : tsupport η.function ⊆ Vreg) (hηW : ∀ x ∈ Wreg, η.function x = 1)
    (hξW : tsupport ξ.function ⊆ Wreg) (hξ2 : ContDiff ℝ 2 ξ.function) (hξT : ∀ x ∈ T, ξ.function x = 1)
    (a b c r s p q t : ℝ) (ha : ∀ i j x, ‖(A i j).function x‖ ≤ a)
    (hb : ∀ i j k x, ‖dcoord (A i j).function x k‖ ≤ b)
    (hc : ∀ i j k l x, ‖dcoord (derivativeMatrix A hA2 k i j).function x l‖ ≤ c)
    (hr : ∀ x, ‖η.function x‖ ≤ r) (hs : ∀ i x, ‖dcoord η.function x i‖ ≤ s)
    (hp : ∀ x, ‖ξ.function x‖ ≤ p) (hq : ∀ i x, ‖dcoord ξ.function x i‖ ≤ q)
    (ht : ∀ i j x, ‖dcoord (derivativeCutoff ξ hξ2 i).function x j‖ ≤ t) :
    let Larr := max (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K P Q)
      (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K K K)
    ∃ f : Space → ℂ, Continuous f ∧ (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ Packet05NormalFluxUniformCeiling.coefficient d a b c r s p q t * Larr := by
  dsimp only
  let DC := firstLocal D0 D1
  let HC := secondLocal H00 H01 H10 H11
  let DF := firstLocal (F1 0) (F1 1)
  let HF := secondLocal (F2 0 0) (F2 0 1) (F2 1 0) (F2 1 1)
  have hDC := first_local_ceiling D0 D1 P hP hD0n hD1n
  have hHC := second_local_ceiling H00 H01 H10 H11 Q hQ hH00n hH01n hH10n hH11n
  have hDF := first_local_ceiling (F1 0) (F1 1) K hK (hF1n 0 (by decide)) (hF1n 1 (by decide))
  have hHF := second_local_ceiling (F2 0 0) (F2 0 1) (F2 1 0) (F2 1 1) K hK
    (hF2n 0 (by decide) 0 (by decide)) (hF2n 0 (by decide) 1 (by decide))
    (hF2n 1 (by decide) 0 (by decide)) (hF2n 1 (by decide) 1 (by decide))
  obtain ⟨hC1,hC2,_,_⟩ := Packet05AssembleTangentialArrays.assemble Vlocal θ hθ2 hθlocal C D0 D1 H00 H01 H10 H11
    hD0 hD1 hH00 hH01 hH10 hH11 aθ bθ cθ haθ hbθ hcθ
  have hDFlocal : ∀ i, i ≠ 2 → ∀ j, HasPartialOn Vlocal (F j) (DF i j) i := by
    intro i hi j
    fin_cases i
    · exact global_partial_on Vlocal _ _ 0 (hF1 0 (by decide) j)
    · exact global_partial_on Vlocal _ _ 1 (hF1 1 (by decide) j)
    · exact (hi rfl).elim
  have hHFlocal : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn Vlocal (DF i j) (HF i t j) t := by
    intro i hi t ht j
    fin_cases i <;> fin_cases t
    · exact global_partial_on Vlocal _ _ 0 (hF2 0 (by decide) 0 (by decide) j)
    · exact global_partial_on Vlocal _ _ 1 (hF2 0 (by decide) 1 (by decide) j)
    · exact (ht rfl).elim
    · exact global_partial_on Vlocal _ _ 0 (hF2 1 (by decide) 0 (by decide) j)
    · exact global_partial_on Vlocal _ _ 1 (hF2 1 (by decide) 1 (by decide) j)
    · exact (ht rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
  obtain ⟨hF1',hF2'⟩ := Packet05QuantitativeLocalArrays.local_arrays Vlocal θ hθ2 hθlocal F DF HF hDFlocal hHFlocal
  let Larr := max (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K P Q)
    (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K K K)
  obtain ⟨hLC,hLF,hLC1,hLF1,hLC2,hLF2⟩ := paired_ceiling θ hθ2 C F DC DF HC HF
    aθ bθ cθ K P Q K K K haθ hbθ hcθ hC hDC hHC hF hDF hHF
  obtain ⟨f,hf,he,hbound⟩ := Packet05LocalizedNormalFluxBound.localized_normal_flux_bound
    Vreg Wreg hWreg hWV A hA2 hA3 C F (first θ C DC) (first θ F DF)
    (second θ hθ2 C DC HC) (second θ hθ2 F DF HF) d hd θ hθV hdiv hC1 hF1' hC2 hF2'
    η ξ hηV hηW hξW hξ2 a b c r s p q t ha hb hc hr hs hp hq ht T hT hTW hξT
  refine ⟨f,hf,he,?_⟩
  intro x
  apply (hbound x).trans
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0 0 0)
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr 0)
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hs 0 0)
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp 0)
  have hq0 : 0 ≤ q := (norm_nonneg _).trans (hq 0 0)
  have ht0 : 0 ≤ t := (norm_nonneg _).trans (ht 0 0 0)
  exact Packet05NormalFluxUniformCeiling.uniform_flux_ceiling (cutVector θ C) (cutVector θ F)
    (first θ C DC) (first θ F DF) (second θ hθ2 C DC HC) (second θ hθ2 F DF HF)
    d a b c r s p q t Larr hd ha0 hb0 hc0 hr0 hs0 hp0 hq0 ht0 hLC hLF hLC1 hLF1 hLC2 hLF2

end OQ14.Packet05RegionalNormalFluxUniform
#print axioms OQ14.Packet05RegionalNormalFluxUniform.regional_normal_flux_uniform
