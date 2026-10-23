import NewtonExteriorResponse
import CompactResponseSmooth

/-! Actual Newton response agrees with the source-separated Hessian integral on an interior source-free ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalInteriorNewton
open MeasureTheory Metric Set OQ14.Maxwell OQ14.GreenKernel OQ14.NewtonExteriorResponse
open scoped SchwartzMap

theorem separation (δ a b : ℝ) (hgap : δ+b ≤ a) (x y : Space)
    (hx : x ∈ ball (0 : Space) b) (hy : y ∉ ball (0 : Space) a) : δ ≤ ‖x-y‖ := by
  have hn := norm_add_le (y-x) x
  rw [sub_add_cancel,norm_sub_rev] at hn
  have hxb : ‖x‖ < b := by simpa only [mem_ball,dist_zero_right] using hx
  have hya : a ≤ ‖y‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hy
  linarith

theorem awayKernel_source_eq (ρ : Space → ℂ) (δ a b : ℝ) (hgap : δ+b ≤ a)
    (hi : ∀ y ∈ ball (0 : Space) a, ρ y=0) (i j : Fin 3) (x y : Space)
    (hx : x ∈ ball (0 : Space) b) :
    ρ y*awayKernel δ i j (x-y)=ρ y*phiHessian 0 (x-y) i j := by
  by_cases hz : ρ y=0
  · simp only [hz,zero_mul]
  · have hy : y ∉ ball (0 : Space) a := fun h => hz (hi y h)
    simp [awayKernel,separation δ a b hgap x y hx hy]

theorem weakConvolution_interior_pairing (ρ : Space → ℂ) (hρ : Integrable ρ)
    (δ a b S : ℝ) (hδ : 0 < δ) (hgap : δ+b ≤ a)
    (hc : ∀ y, y ∉ closedBall (0 : Space) S → ρ y=0)
    (hi : ∀ y ∈ ball (0 : Space) a, ρ y=0) (i j : Fin 3)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) b) :
    NewtonConvolution.weakConvolution ρ i j f.val=
      ∫ x, KernelConvolution.response (awayKernel δ i j) ρ x*f.val x := by
  rw [KernelConvolution.response_pairing _ _ (awayKernel_locallyIntegrable δ hδ i j)
    hρ (source_compact ρ S hc) f]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ y=0
  · simp only [hz,zero_mul]
  have hy : y ∉ ball (0 : Space) a := fun h => hz (hi y h)
  have hfy : y ∉ tsupport (f.val : Space → ℂ) := by
    intro h
    have hb : ‖y‖ < b := by simpa only [mem_ball,dist_zero_right] using hf h
    apply hy
    simp only [mem_ball,dist_zero_right]
    linarith
  rw [FieldResponse.weakHessian_symmetric i j,NewtonExterior.translated_weakHessian_away i j f y hfy]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f.val x=0
  · simp only [hx,mul_zero]
  have hs := separation δ a b hgap x y (hf (subset_tsupport _ hx)) hy
  simp [awayKernel,hs]

theorem newton_cutResponse_pairing (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ a b S : ℝ) (hδ : 0 < δ) (hgap : δ+b ≤ a)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0)
    (i : Fin 3) (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x*f.val x)=
      ∫ x, cutResponse δ ρ x i*f.val x := by
  rw [NewtonL1L2.newtonOperator_spatial_pairing F (fun j => (hρ j).congr (hF j).symm)]
  simp only [cutResponse,Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => FieldResponse.response_test_integrable _ (ρ j)
    (awayKernel_locallyIntegrable δ hδ i j) (hρ j) (source_compact _ S (hc j)) f)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← weakConvolution_interior_pairing (ρ j) (hρ j) δ a b S hδ hgap (hc j) (hi j) i j f hf]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards [hF j] with y hy
  rw [hy]

theorem newton_ae_cutResponse (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ a b S : ℝ) (hδ : 0 < δ) (hgap : δ+b ≤ a)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x=cutResponse δ ρ x i := by
  have hN := (Lp.memLp (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i)).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hC := cutResponse_locallyIntegrable F ρ hρ hF δ S hδ hc i
  have hz := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x-cutResponse δ ρ x i)
    ((hN.sub hC).locallyIntegrableOn (ball (0 : Space) b))
  have hh : ∀ (g : Space → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ ball (0 : Space) b →
      (∫ x, g x • (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x-cutResponse δ ρ x i))=0 := by
    intro g hg hgc hgU
    have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left (g := Complex.ofReal) (by simp)
    let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz (fun x => (g x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg) hgc',hgc'⟩
    have hs : tsupport (f.val : Space → ℂ)=tsupport g := by
      change closure (Function.support (fun x => (g x : ℂ)))=closure (Function.support g)
      ext x
      simp [Function.support]
    have hp := newton_cutResponse_pairing F ρ hρ hF δ a b S hδ hgap hc hi i f (hs ▸ hgU)
    have hn := NewtonL2.scalar_pairing_integrable (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
    have hd := cutResponse_test_integrable ρ hρ δ S hδ hc i f
    have he : (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x*f.val x-
        cutResponse δ ρ x i*f.val x)=0 := by
      rw [integral_sub hn hd,hp,sub_self]
    convert he using 1
    apply integral_congr_ae
    filter_upwards with x
    change (g x : ℂ)*(_-_)=_*(g x : ℂ)-_*(g x : ℂ)
    ring
  filter_upwards [hz hh] with x hx hm
  exact sub_eq_zero.mp (hx hm)

theorem newton_ae_interior (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a b S : ℝ) (hba : b < a)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x=
        ∑ j, ∫ y, ρ j y*phiHessian 0 (x-y) i j := by
  have hd : 0 < (a-b)/2 := by linarith
  have hg : (a-b)/2+b ≤ a := by linarith
  filter_upwards [newton_ae_cutResponse F ρ hρ hF ((a-b)/2) a b S hd hg hc hi i] with x hx hm
  rw [hx hm]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  exact awayKernel_source_eq (ρ j) ((a-b)/2) a b hg (hi j) i j x y hm

end OQ14.ConicalInteriorNewton

#print axioms OQ14.ConicalInteriorNewton.separation
#print axioms OQ14.ConicalInteriorNewton.awayKernel_source_eq
#print axioms OQ14.ConicalInteriorNewton.weakConvolution_interior_pairing
#print axioms OQ14.ConicalInteriorNewton.newton_cutResponse_pairing
#print axioms OQ14.ConicalInteriorNewton.newton_ae_cutResponse
#print axioms OQ14.ConicalInteriorNewton.newton_ae_interior
