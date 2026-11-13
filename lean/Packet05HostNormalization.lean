import Packet05ActualModeGraphEquation

/-! Normalize a positive constant host dielectric before applying the flat
binary scalar transmission theory; all identities are regional. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05HostNormalization
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05FlatWeight
  OQ14.Packet05LocalDerivative

theorem regional_divergence_smul (V : Set Space) (P : L2Vector) (a : ℂ)
    (h : HasDivergenceOn V P 0) : HasDivergenceOn V (fun j => a • P j) 0 := by
  intro φ hφ
  have hh := h φ hφ
  simp only [map_zero,zero_add] at hh ⊢
  simp only [map_smul,smul_eq_mul]
  linear_combination a*hh

theorem normalized_constitutive_ae (V : Set Space) (P G Q : L2Vector) (ε : Space → ℂ)
    (host : ℂ)
    (hP : ∀ j, (fun x => P j x) =ᵐ[volume] fun x => ε x*(G j x+Q j x)) (j : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ V → (host⁻¹ • P j : L2Scalar) x =
      (host⁻¹*ε x)*(G j x+Q j x) := by
  filter_upwards [hP j,Lp.coeFn_smul host⁻¹ (P j)] with x hp hs _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hp]
  ring

theorem normalized_binary_match_ae (W : Set Space) (ε : Space → ℂ) (host : ℂ) (d : ℝ)
    (hhost : host ≠ 0)
    (hmaterial : ∀ x ∈ W, ε x = host * (if x 2 < 0 then (1 : ℂ) else if x 2 = 0 then 1 else 1+d)) :
    ∀ᵐ x ∂volume, x ∈ W → host⁻¹*ε x = weight d x := by
  have hn : ∀ᵐ x : Space ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  filter_upwards [hn] with x hx hW
  rw [hmaterial x hW]
  by_cases hneg : x 2 < 0
  · simp [weight,FlatDifferenceCoercivity.dielectric,hneg,hhost]
  · simp [weight,FlatDifferenceCoercivity.dielectric,hneg,hx,hhost]

end OQ14.Packet05HostNormalization
#print axioms OQ14.Packet05HostNormalization.regional_divergence_smul
#print axioms OQ14.Packet05HostNormalization.normalized_constitutive_ae
#print axioms OQ14.Packet05HostNormalization.normalized_binary_match_ae
