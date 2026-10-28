import SourceFreeOpenResponse
import ConicalSourceFreeHelmholtz
import DisjointBallGeometry
import HelmholtzUniqueContinuation
import ConicalRungeAnnihilator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceFreeOpenHelmholtz
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.RegionalMaxwellHelmholtz OQ14.WeakHelmholtzRegularity
open scoped Topology
abbrev Space := Maxwell.Space

theorem source_pair_zero (ρ : Space → ℂ) (U : Set Space)
    (hi : ∀ y ∈ U, ρ y = 0) (f : Test U) : (∫ x : Space, ρ x*f.val x)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  simp only [Pi.zero_apply]
  by_cases hx : f.val x=0
  · rw [hx,mul_zero]
  · rw [hi x (f.property.2.2 (subset_tsupport _ hx)),zero_mul]

theorem regional_maxwell (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (U : Set Space) (hi : ∀ j y, y ∈ U → ρ j y=0) :
    TestMaxwell k 1 U (FieldResponse.electric k F ρ) (MagneticResponse.magnetic k ρ) := by
  intro i f
  constructor
  · exact MagneticResponse.electric_curl_pairing k F ρ hρ hc hF i (ConicalInnerMaxwell.globalTest f)
  · have h := MagneticResponse.magnetic_curl_pairing k F ρ hρ hc hF i (ConicalInnerMaxwell.globalTest f)
    change curlPair (fieldPair (MagneticResponse.magnetic k ρ)) i f=
      -(Complex.I*(k : ℂ))*(fieldPair (FieldResponse.electric k F ρ) i f+(∫ x, ρ i x*f.val x)) at h
    simpa only [source_pair_zero (ρ i) U (hi i) f,add_zero,Complex.ofReal_one,mul_one] using h

theorem electric_weak (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (U : Set Space) (hi : ∀ j y, y ∈ U → ρ j y=0) (i : Fin 3) :
    IsWeakHelmholtz (k : ℂ) U (fun x => FieldResponse.electric k F ρ x i) := by
  have hE : IntegrableTests U (FieldResponse.electric k F ρ) := fun j f =>
    FieldResponse.electric_test_integrable k F ρ hρ hc j (ConicalInnerMaxwell.globalTest f)
  simpa only [Real.sqrt_one,mul_one] using RegionalMaxwellHelmholtz.electric_weak_helmholtz k 1 hk
    (by norm_num) _ _ _ (regional_maxwell k F ρ hρ hc hF U hi) hE i

theorem integral_weak (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y=0) (i : Fin 3) :
    IsWeakHelmholtz (k : ℂ) U (fun x => ExteriorContinuity.electric k ρ x i) := by
  intro φ hφ hcomp hs
  have hc' : ∀ j, HasCompactSupport (ρ j) := fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)
  have hw := electric_weak k hk F ρ hρ hc' hF U hi i φ hφ hcomp hs
  have he : (∫ x, ExteriorContinuity.electric k ρ x i*(ExteriorHelmholtz.laplacian φ x+(k : ℂ)^2*φ x))=
      ∫ x, FieldResponse.electric k F ρ x i*(ExteriorHelmholtz.laplacian φ x+(k : ℂ)^2*φ x) := by
    apply integral_congr_ae
    filter_upwards [SourceFreeOpenResponse.electric_ae k F ρ hρ hF S hc U hU hi] with x hx
    by_cases hm : x ∈ U
    · rw [congrFun (hx hm) i]
    · have hn : x ∉ tsupport φ := fun h => hm (hs h)
      rw [ExteriorGreen.laplacian_zero_of_not_tsupport hn,image_eq_zero_of_nmem_tsupport hn]
      simp
  exact he.trans hw

theorem electric_classical (k : ℝ) (hk : k≠0) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (U : Set Space) (hU : IsOpen U) (hi : ∀ j y, y ∈ U → ρ j y=0) (i : Fin 3) (x : Space)
    (hx : x ∈ U) :
    ExteriorHelmholtz.laplacian (fun y => ExteriorContinuity.electric k ρ y i) x+
      (k : ℂ)^2*ExteriorContinuity.electric k ρ x i=0 := by
  apply UniformHelmholtzEquation.classical_of_weak U hU k _ _
    (integral_weak k hk F ρ hρ hF S hc U hU hi i) x hx
  intro y hy
  exact (SourceFreeOpenResponse.electric_smooth k ρ hρ
    (fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)) U hU hi i y hy).contDiffAt (hU.mem_nhds hy)
theorem annihilator_zero_exterior {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hS : 0 ≤ S) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ DisjointBallGeometry.exterior center radius → ρ j y=0)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, ConicalRungeAnnihilator.planePair k ρ n i=0) :
    ∀ x ∈ DisjointBallGeometry.exterior center radius, ExteriorContinuity.electric k ρ x=0 := by
  let U := DisjointBallGeometry.exterior center radius
  have hU : IsOpen U := DisjointBallGeometry.exterior_isOpen center radius
  have hconn : IsPreconnected U := (DisjointBallGeometry.exterior_isConnected center radius hr hsep).isPreconnected
  obtain ⟨c,hcU,hcS⟩ := DisjointBallGeometry.exists_exterior_outside center radius S
  intro x hx
  ext i
  have hzero : (fun y => ExteriorContinuity.electric k ρ y i) =ᶠ[𝓝 c] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hcS] with y hy
    simp only [Pi.zero_apply]
    rw [ConicalRungeAnnihilator.exterior_zero k hk S hS ρ hρ hc h y hy]
    rfl
  exact HelmholtzUniqueContinuation.zero_on_connected_open U hU hconn (k : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hk)) _
    (SourceFreeOpenResponse.electric_smooth k ρ hρ
      (fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)) U hU hi i)
    (fun y hy => electric_classical k (ne_of_gt hk) F ρ hρ hF S hc U hU hi i y hy)
    c hcU hzero x hx
theorem reciprocal_pair_zero {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
    (F G : VectorFourier.VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hcρ : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hcσ : ∀ j y, y ∉ closedBall (0 : Space) T → σ j y=0)
    (hiρ : ∀ j y, y ∈ DisjointBallGeometry.exterior center radius → ρ j y=0)
    (hiσ : ∀ j y, y ∉ DisjointBallGeometry.exterior center radius → σ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, ConicalRungeAnnihilator.planePair k ρ n i=0) :
    (∑ i : Fin 3, ∫ x, FieldResponse.electric k G σ x i*ρ i x)=0 := by
  have hcρT (j : Fin 3) (x : Space) (hx : x ∉ closedBall (0 : Space) T) : ρ j x=0 :=
    hcρ j x (fun hn => hx (closedBall_subset_closedBall hST hn))
  rw [NewtonReciprocity.electric_compact_L2_reciprocity k T G F σ ρ hcσ hcρT hG hF]
  have hρ := NewtonReciprocity.compact_source_integrable S F ρ hcρ hF
  have he := SourceFreeOpenResponse.electric_ae k F ρ hρ hF S hcρ
    (DisjointBallGeometry.exterior center radius) (DisjointBallGeometry.exterior_isOpen center radius) hiρ
  have hz := annihilator_zero_exterior center radius hr hsep k hk F ρ hρ hF S hS hcρ hiρ h
  apply Finset.sum_eq_zero
  intro i _
  apply integral_eq_zero_of_ae
  filter_upwards [he] with x hx
  by_cases hm : x ∈ DisjointBallGeometry.exterior center radius
  · rw [hx hm, hz x hm]
    simp
  · simp [hiσ i x hm]
end OQ14.SourceFreeOpenHelmholtz
#print axioms OQ14.SourceFreeOpenHelmholtz.source_pair_zero
#print axioms OQ14.SourceFreeOpenHelmholtz.regional_maxwell
#print axioms OQ14.SourceFreeOpenHelmholtz.electric_weak
#print axioms OQ14.SourceFreeOpenHelmholtz.integral_weak
#print axioms OQ14.SourceFreeOpenHelmholtz.electric_classical


#print axioms OQ14.SourceFreeOpenHelmholtz.annihilator_zero_exterior


#print axioms OQ14.SourceFreeOpenHelmholtz.reciprocal_pair_zero

