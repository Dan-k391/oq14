import ConicalProjectionLocalization
import NewtonReciprocity

/-! Actual compact-source Green potentials construct spatial projection systems in a fixed source gauge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCompactPotential
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalGradientGraph
  OQ14.ConicalProjectionData
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def potentialData (k S : ℝ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j) : PotentialData where
  potential := ElectricPotentialDecomposition.potential k ρ
  derivative i x := FieldResponse.electric k F ρ x i-ElectricPotentialDecomposition.correction k ρ x i
  potential_memLp R := ElectricPotentialDecomposition.potential_memLp_ball k R S F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF) hc hF
  derivative_memLp R i := ElectricPotentialDecomposition.gradient_memLp_ball k R S F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF) hc hF i
  weak := ElectricPotentialDecomposition.potential_weak_partial k F ρ
    (NewtonReciprocity.compact_source_integrable S F ρ hc hF)
    (fun j => HasCompactSupport.intro' (isCompact_closedBall (0 : Space) S) isClosed_closedBall (hc j)) hF

def system (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn) (k S : ℝ)
    (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
      (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        (FieldResponse.electric k F ρ x i+J x i)*dcoord f x i)=0) : System p a :=
  ConicalProjectionLocalization.ofPotential p a hai (potentialData k S F ρ hc hF)
    (fun x i => J x i+ElectricPotentialDecomposition.correction k ρ x i)
    (fun i => (hJ i).add (ElectricPotentialDecomposition.correction_continuous k S F ρ hc hF i))
    (by
      intro f hf
      have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
          ((potentialData k S F ρ hc hF).derivative i x+
            (J x i+ElectricPotentialDecomposition.correction k ρ x i))*dcoord f x i)=
          ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
            (FieldResponse.electric k F ρ x i+J x i)*dcoord f x i := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [potentialData]
        ring
      simpa only [he] using hGauss f hf)

theorem total_inner (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn) (k S : ℝ)
    (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
      (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        (FieldResponse.electric k F ρ x i+J x i)*dcoord f x i)=0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) a →
      totalCoordinate (system p a hai k S F ρ hc hF J hJ hGauss) i x=
        FieldResponse.electric k F ρ x i+J x i := by
  filter_upwards [totalCoordinate_ae (system p a hai k S F ρ hc hF J hJ hGauss) i,
    gradient_ae p.cutoff (potentialData k S F ρ hc hF) i] with x ht hg
  intro hm
  have hx := bump_inner p.cutoff x (ball_subset_ball hai.le hm)
  rw [ht]
  change gradient p.cutoff (potentialData k S F ρ hc hF) i x+
    bump p.cutoff x*(J x i+ElectricPotentialDecomposition.correction k ρ x i)=_
  rw [hg,hx.1,hx.2 i]
  dsimp only [potentialData]
  ring

end OQ14.ConicalCompactPotential

#print axioms OQ14.ConicalCompactPotential.potentialData
#print axioms OQ14.ConicalCompactPotential.system
#print axioms OQ14.ConicalCompactPotential.total_inner
