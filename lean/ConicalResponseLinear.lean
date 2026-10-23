import ConicalCompactPotential

/-! Actual compact-source response subtraction and continuous correction control. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalResponseLinear
open MeasureTheory Metric Set OQ14.Maxwell OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

theorem source_sub_ae (F G : VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hF : ∀ j, (physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) (i : Fin 3) :
    (physicalCoordinate (F-G) i : Space → ℂ) =ᵐ[volume] fun x => ρ i x-σ i x := by
  simp only [physicalCoordinate,map_sub]
  filter_upwards [Lp.coeFn_sub (physicalCoordinate F i) (physicalCoordinate G i),hF i,hG i]
    with x hs hf hg
  change (physicalCoordinate F i-physicalCoordinate G i) x=_
  rw [hs]
  simp only [Pi.sub_apply,hf,hg]

theorem electric_sub_ae (k R S : ℝ) (F G : VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hF : ∀ j, (physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (hρ : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hσ : ∀ j y, y ∉ closedBall (0 : Space) S → σ j y=0) (i : Fin 3) :
    (fun x => FieldResponse.electric k (F-G) (fun j y => ρ j y-σ j y) x i)
      =ᵐ[volume.restrict (closedBall (0 : Space) R)]
        fun x => FieldResponse.electric k F ρ x i-FieldResponse.electric k G σ x i := by
  have hd := source_sub_ae F G ρ σ hF hG
  have hzero : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y-σ j y=0 :=
    fun j y hy => by rw [hρ j y hy,hσ j y hy,sub_self]
  have hl : LocalVolumeResponse.localRepresentative k R S (F-G)=
      LocalVolumeResponse.localRepresentative k R S F-LocalVolumeResponse.localRepresentative k R S G := by
    simp only [LocalVolumeResponse.localRepresentative,map_sub]
    abel
  have hp : ∀ᵐ x : Space, physicalCoordinate (LocalVolumeResponse.localRepresentative k R S (F-G)) i x=
      physicalCoordinate (LocalVolumeResponse.localRepresentative k R S F) i x-
        physicalCoordinate (LocalVolumeResponse.localRepresentative k R S G) i x := by
    rw [hl]
    exact source_sub_ae _ _ _ _ (fun j => Filter.EventuallyEq.rfl) (fun j => Filter.EventuallyEq.rfl) i
  filter_upwards [LocalVolumeResponse.electric_ae_on_ball k R S (F-G) _
    (NewtonReciprocity.compact_source_integrable S (F-G) _ hzero hd) hzero hd i,
    LocalVolumeResponse.electric_ae_on_ball k R S F ρ
      (NewtonReciprocity.compact_source_integrable S F ρ hρ hF) hρ hF i,
    LocalVolumeResponse.electric_ae_on_ball k R S G σ
      (NewtonReciprocity.compact_source_integrable S G σ hσ hG) hσ hG i,
    ae_restrict_of_ae hp] with x hd hf hg hp
  rw [← hd,← hf,← hg,hp]

theorem correction_sub (k S : ℝ) (F G : VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hF : ∀ j, (physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (hρ : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hσ : ∀ j y, y ∉ closedBall (0 : Space) S → σ j y=0) (i : Fin 3) (x : Space) :
    ElectricPotentialDecomposition.correction k (fun j y => ρ j y-σ j y) x i=
      ElectricPotentialDecomposition.correction k ρ x i-ElectricPotentialDecomposition.correction k σ x i := by
  have hx : x ∈ closedBall (0 : Space) ‖x‖ := by simp
  simp only [ElectricPotentialDecomposition.correction,KernelConvolution.response,sub_mul]
  rw [integral_sub
    (ScalarPotentialBound.response_integrable k ‖x‖ S (ρ i) (physicalCoordinate F i) (hF i) (hρ i) x hx)
    (ScalarPotentialBound.response_integrable k ‖x‖ S (σ i) (physicalCoordinate G i) (hG i) (hσ i) x hx),mul_sub]

theorem correction_difference_bound (k R S : ℝ) (F G : VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hF : ∀ j, (physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (hρ : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hσ : ∀ j y, y ∉ closedBall (0 : Space) S → σ j y=0)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) R) :
    ‖ElectricPotentialDecomposition.correction k ρ x i-ElectricPotentialDecomposition.correction k σ x i‖ ≤
      k^2*‖physicalCoordinate (F-G) i‖*‖ScalarPotentialBound.cutoff 0 (R+S)‖ := by
  rw [← correction_sub k S F G ρ σ hF hG hρ hσ i x]
  exact ScalarPotentialBound.scaled_response_bound k R S _ (physicalCoordinate (F-G) i)
    (source_sub_ae F G ρ σ hF hG i)
    (fun y hy => by rw [hρ i y hy,hσ i y hy,sub_self]) x hx

end OQ14.ConicalResponseLinear
#print axioms OQ14.ConicalResponseLinear.source_sub_ae
#print axioms OQ14.ConicalResponseLinear.electric_sub_ae
#print axioms OQ14.ConicalResponseLinear.correction_sub
#print axioms OQ14.ConicalResponseLinear.correction_difference_bound
