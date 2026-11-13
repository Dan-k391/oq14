import Packet05RegionalDivergenceCongruence
import Packet05ScalarDielectricFlux

/-! An interior plateau may localize graph fields without changing the
regional transmission equation or conserved flux on that plateau. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PlateauGraphFlux
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05RegionalDivergenceCongruence Packet05ScalarDielectricFlux

def cutVector (θ : Test) (C : L2Vector) : L2Vector :=
  fun j => scaleL2 θ.function θ.regular.continuous θ.compact (C j)

theorem plateau_flux (V : Set Space) (θ : Test) (hθ : ∀ x ∈ V, θ.function x = 1)
    (A : Fin 3 → Fin 3 → Test) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d) :
    ∀ j, ∀ᵐ x ∂volume, x ∈ V →
      (flux A (cutVector θ C) d hd j-cutVector θ F j : L2Scalar) x =
        (flux A C d hd j-F j : L2Scalar) x := by
  have hC (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → cutVector θ C j x = C j x := by
    filter_upwards [scaleL2_ae θ.function θ.regular.continuous θ.compact (C j)] with x hx hVx
    change (scaleL2 θ.function θ.regular.continuous θ.compact (C j)) x = _
    rw [hx,hθ x hVx,one_mul]
  have hF (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → cutVector θ F j x = F j x := by
    filter_upwards [scaleL2_ae θ.function θ.regular.continuous θ.compact (F j)] with x hx hVx
    change (scaleL2 θ.function θ.regular.continuous θ.compact (F j)) x = _
    rw [hx,hθ x hVx,one_mul]
  intro j
  filter_upwards [flux_local_ae_eq V A C (cutVector θ C) d hd hC j,hF j,
    Lp.coeFn_sub (flux A (cutVector θ C) d hd j) (cutVector θ F j),
    Lp.coeFn_sub (flux A C d hd j) (F j)] with x ha hb hc he hx
  rw [hc,he]
  simp only [Pi.sub_apply,ha hx,hb hx]

theorem plateau_divergence (V : Set Space) (θ : Test) (hθ : ∀ x ∈ V, θ.function x = 1)
    (A : Fin 3 → Fin 3 → Test) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0) :
    HasDivergenceOn V (fun j => flux A (cutVector θ C) d hd j-cutVector θ F j) 0 := by
  exact divergence_on_of_ae_eq V _ _ 0 hdiv (plateau_flux V θ hθ A C F d hd)

end OQ14.Packet05PlateauGraphFlux
#print axioms OQ14.Packet05PlateauGraphFlux.plateau_flux
#print axioms OQ14.Packet05PlateauGraphFlux.plateau_divergence
