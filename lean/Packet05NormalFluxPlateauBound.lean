import Packet05NormalFluxOriginalBound

/-! Plateau transfer of the explicit original-data normal-flux estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet05NormalFluxPlateauBound
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05ScalarDielectricFlux Packet05PartialProduct
  Packet05NormalFluxArrays Packet05NormalFluxNorms Packet05NormalFluxDataBounds
  Packet05FirstNormalFluxDataBound Packet05NormalFluxOriginalBound Packet05MatrixWeakDerivative MaxwellCutoffCommutator

theorem normal_flux_plateau_bound (V W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (C j) (C1 i j) i)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hC2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (η χ : Test) (hηV : tsupport η.function ⊆ V)
    (hηW : ∀ x ∈ W, η.function x = 1) (hχW : tsupport χ.function ⊆ W)
    (hχ2 : ContDiff ℝ 2 χ.function) (a b c r s p q t : ℝ)
    (ha : ∀ i j x, ‖(A i j).function x‖ ≤ a)
    (hb : ∀ i j k x, ‖dcoord (A i j).function x k‖ ≤ b)
    (hc : ∀ i j k l x, ‖dcoord (derivativeMatrix A hA2 k i j).function x l‖ ≤ c)
    (hr : ∀ x, ‖η.function x‖ ≤ r) (hs : ∀ i x, ‖dcoord η.function x i‖ ≤ s)
    (hp : ∀ x, ‖χ.function x‖ ≤ p) (hq : ∀ i x, ‖dcoord χ.function x i‖ ≤ q)
    (ht : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ t)
    (T : Set Space) (hT : IsOpen T) (hTW : T ⊆ W)
    (hχT : ∀ x ∈ T, χ.function x = 1) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((p+3*q+6*t)*r*((1+d)*a*size C+‖F 2‖) +
         (p+2*q)*3*firstBound C F C1 F1 d a b r s +
         ∑ i : Fin 2, ∑ _j : Fin 3, secondBound C C1 F1 C2 F2 d a b c p q i.castSucc) := by
  obtain ⟨f,hf,hae,hbound⟩ := Packet05NormalFluxOriginalBound.normal_flux_original_bound
    V W hW hWV A hA2 hA3 C F C1 F1 C2 F2 d hd hdiv hC1 hF1 hC2 hF2 η χ
    hηV hηW hχW hχ2 a b c r s p q t ha hb hc hr hs hp hq ht
  refine ⟨f,hf,?_,hbound⟩
  apply (ae_restrict_iff' hT.measurableSet).mpr
  filter_upwards [hae,
    scaleL2_ae χ.function χ.regular.continuous χ.compact
      (scaleL2 η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)),
    scaleL2_ae η.function η.regular.continuous η.compact (flux A C d hd 2-F 2)] with x hx hχ hη hxT
  rw [hχ,hη,hχT x hxT,hηW x (hTW hxT),one_mul,one_mul] at hx
  exact hx

end OQ14.Packet05NormalFluxPlateauBound
#print axioms OQ14.Packet05NormalFluxPlateauBound.normal_flux_plateau_bound
