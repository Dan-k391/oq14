import ConicalInteriorResponse
import UniformHelmholtzEquation
import ConicalInnerMaxwell

/-! Actual source-free compact Green electric fields solve classical interior Helmholtz. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalSourceFreeHelmholtz
open MeasureTheory Set Metric OQ14.Maxwell OQ14.RegionalMaxwellHelmholtz OQ14.WeakHelmholtzRegularity
open scoped Topology
abbrev Space := Maxwell.Space

theorem source_pair_zero (ρ : Space → ℂ) (a : ℝ)
    (hi : ∀ y ∈ ball (0 : Space) a, ρ y=0) (f : Test (ball (0 : Space) a)) :
    (∫ x : Space, ρ x*f.val x)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  simp only [Pi.zero_apply]
  by_cases hx : f.val x=0
  · rw [hx,mul_zero]
  · rw [hi x (f.property.2.2 (subset_tsupport _ hx)),zero_mul]

theorem regional_maxwell (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a : ℝ) (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) :
    TestMaxwell k 1 (ball (0 : Space) a) (FieldResponse.electric k F ρ) (MagneticResponse.magnetic k ρ) := by
  intro i f
  constructor
  · exact MagneticResponse.electric_curl_pairing k F ρ hρ hc hF i (ConicalInnerMaxwell.globalTest f)
  · have h := MagneticResponse.magnetic_curl_pairing k F ρ hρ hc hF i (ConicalInnerMaxwell.globalTest f)
    change curlPair (fieldPair (MagneticResponse.magnetic k ρ)) i f=
      -(Complex.I*(k : ℂ))*(fieldPair (FieldResponse.electric k F ρ) i f+(∫ x, ρ i x*f.val x)) at h
    simpa only [source_pair_zero (ρ i) a (hi i) f,add_zero,Complex.ofReal_one,mul_one] using h

theorem electric_weak_helmholtz (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a : ℝ) (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) :
    IsWeakHelmholtz (k : ℂ) (ball (0 : Space) a) (fun x => FieldResponse.electric k F ρ x i) := by
  have hE : IntegrableTests (ball (0 : Space) a) (FieldResponse.electric k F ρ) := fun j f =>
    FieldResponse.electric_test_integrable k F ρ hρ hc j (ConicalInnerMaxwell.globalTest f)
  simpa only [Real.sqrt_one,mul_one] using RegionalMaxwellHelmholtz.electric_weak_helmholtz k 1 hk
    (by norm_num) _ _ _ (regional_maxwell k F ρ hρ hc hF a hi) hE i

theorem integral_weak_helmholtz (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) :
    IsWeakHelmholtz (k : ℂ) (ball (0 : Space) a) (fun x => ExteriorContinuity.electric k ρ x i) := by
  intro φ hφ hcomp hs
  have hc' : ∀ j, HasCompactSupport (ρ j) := fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)
  have hw := electric_weak_helmholtz k hk F ρ hρ hc' hF a hi i φ hφ hcomp hs
  have he : (∫ x, ExteriorContinuity.electric k ρ x i*(ExteriorHelmholtz.laplacian φ x+(k : ℂ)^2*φ x))=
      ∫ x, FieldResponse.electric k F ρ x i*(ExteriorHelmholtz.laplacian φ x+(k : ℂ)^2*φ x) := by
    apply integral_congr_ae
    filter_upwards [ConicalInteriorResponse.electric_ae_interior k F ρ hρ hF a S hc hi] with x hx
    by_cases hm : x ∈ ball (0 : Space) a
    · rw [congrFun (hx hm) i]
    · have hn : x ∉ tsupport φ := fun h => hm (hs h)
      rw [ExteriorGreen.laplacian_zero_of_not_tsupport hn,image_eq_zero_of_nmem_tsupport hn]
      simp
  exact he.trans hw

theorem electric_classical_helmholtz (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) (x : Space)
    (hx : x ∈ ball (0 : Space) a) :
    ExteriorHelmholtz.laplacian (fun y => ExteriorContinuity.electric k ρ y i) x+
      (k : ℂ)^2*ExteriorContinuity.electric k ρ x i=0 := by
  apply UniformHelmholtzEquation.classical_of_weak _ isOpen_ball k _ _
    (integral_weak_helmholtz k hk F ρ hρ hF a S hc hi i) x hx
  intro y hy
  exact ConicalInteriorResponse.electric_smooth_interior k ρ hρ
    (fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)) a hi i y hy

end OQ14.ConicalSourceFreeHelmholtz

#print axioms OQ14.ConicalSourceFreeHelmholtz.source_pair_zero
#print axioms OQ14.ConicalSourceFreeHelmholtz.regional_maxwell
#print axioms OQ14.ConicalSourceFreeHelmholtz.electric_weak_helmholtz
#print axioms OQ14.ConicalSourceFreeHelmholtz.integral_weak_helmholtz
#print axioms OQ14.ConicalSourceFreeHelmholtz.electric_classical_helmholtz
