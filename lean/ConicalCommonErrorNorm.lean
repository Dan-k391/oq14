import ConicalCommonErrorBridge

/-! Local representative of the simultaneous union-Runge incident error. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonErrorNorm
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.UnionFreeRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def target (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) :=
  UnionFreeRunge.target k R T (balls center a) hKR (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ConicalCommonBaseline.source_ae p a center i)

def errorVector (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) : Vector (balls center a) :=
  UnionFiniteAngularRunge.incident k R (balls center a) hKR d + target p a center ha i R T k hKR hT

def localError (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) (j : Fin 3) : ConicalRungeBall.ScalarBall (a i) :=
  ConicalBallRestriction.scalar (a i) (StaticBallTranslation.scalar (-center i)
    (UnionMaterialTransfer.scalarExtension (balls center a) (balls_compact center a).measurableSet
      (errorVector p a center ha i R T k hKR hT d j)))

omit [DecidableEq ι] in
theorem localError_norm (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) (j : Fin 3) :
    ‖localError p a center ha i R T k hKR hT d j‖ ≤ ‖errorVector p a center ha i R T k hKR hT d‖ := by
  apply (ConicalBallRestriction.scalarRestriction_norm _ _).trans
  rw [(StaticBallTranslation.scalar (-center i)).norm_map, UnionMaterialTransfer.scalarExtension_norm]
  exact PiLp.norm_apply_le _ j

include hsep in
theorem localError_ae (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (j : Fin 3) :
    (localError p a center ha i R T k hKR hT d j : Space → ℂ) =ᵐ[volume.restrict (ball (0 : Space) (a i))]
      ConicalCommonIncidentError.error (p i) (a i) k (center i) d j := by
  let K := balls center a
  have hK := (balls_compact center a).measurableSet
  have htarget := (ae_restrict_iff' hK).mp (CommonUnionTarget.target_negative_incident p a center ha i R T k hKR hT j)
  have hang := (ae_restrict_iff' hK).mp (UnionFiniteAngularRunge.incident_ae k R K hKR d j)
  have hadd := (ae_restrict_iff' hK).mp (Lp.coeFn_add (UnionFiniteAngularRunge.incident k R K hKR d j)
    (target p a center ha i R T k hKR hT j))
  have hs := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae
    (htarget.and (hang.and hadd))
  have he := ConicalCommonErrorBridge.incident_centered_ae p a center ha hsep i R T k
    hR hT hai j
  have hxres := ConicalBallRestriction.scalarRestriction_ae (a i)
    (StaticBallTranslation.scalar (-center i) (UnionMaterialTransfer.scalarExtension K hK (errorVector p a center ha i R T k hKR hT d j)))
  filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hxres,
    ae_restrict_of_ae (StaticBallTranslation.scalar_ae (-center i)
      (UnionMaterialTransfer.scalarExtension K hK (errorVector p a center ha i R T k hKR hT d j))),
    ae_restrict_of_ae ((measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae
      (UnionMaterialTransfer.scalarExtension_ae K hK (errorVector p a center ha i R T k hKR hT d j))),
    ae_restrict_of_ae hs, ae_restrict_of_ae he, ae_restrict_mem isOpen_ball.measurableSet] with x hr ht hext hs he hx
  have hm : x+center i ∈ closedBall (center i) (a i) := by
    have hn : ‖x‖ < a i := by simpa using hx
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right] using hn.le
  have hmem : x+center i ∈ K := Set.mem_iUnion.mpr ⟨i,hm⟩
  have htarg : target p a center ha i R T k hKR hT j (x+center i) =
    -physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j (x+center i) := hs.1 hmem
  change ConicalBallRestriction.scalarRestriction (a i) _ x = _
  rw [hr, ht]
  simp only [sub_neg_eq_add] at *
  rw [hext, indicator_of_mem hmem]
  change (UnionFiniteAngularRunge.incident k R K hKR d j + target p a center ha i R T k hKR hT j) (x+center i) = _
  rw [hs.2.2 hmem]
  simp only [Pi.add_apply, hs.2.1 hmem, htarg, he hx, neg_neg, ConicalCommonIncidentError.error, add_comm]

include hsep in
theorem localError_ae_closed (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (j : Fin 3) :
    (localError p a center ha i R T k hKR hT d j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) (a i))]
      ConicalCommonIncidentError.error (p i) (a i) k (center i) d j := by
  have he := (ae_restrict_iff' isOpen_ball.measurableSet).mp (localError_ae p a center ha hsep i R T k hKR hR hT hai d j)
  filter_upwards [ae_restrict_of_ae he, ae_restrict_of_ae (OQ14.RadialInterface.ae_regular (a i)),
    ae_restrict_mem measurableSet_closedBall] with x he hr hx
  have hn : ‖x‖ < a i := lt_of_le_of_ne (by simpa using hx) hr.2
  exact he (by simpa using hn)

include hsep in
theorem uniform_error_bound (i : ι) (R T k b : ℝ) (hk : k ≠ 0) (hb : b < a i)
    (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Input) (j : Fin 3) x, x ∈ closedBall (0 : Space) b →
      ‖ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x‖ ≤
        C * ‖errorVector p a center ha i R T k hKR hT d‖ := by
  obtain ⟨C,hC,hbound⟩ := ConicalCommonIncidentError.uniform_error_bound (p i) (a i) b k (hai i) hb hk (center i)
  refine ⟨C,hC,?_⟩
  intro d j x hx
  exact (hbound d j (localError p a center ha i R T k hKR hT d j)
    (localError_ae_closed p a center ha hsep i R T k hKR hR hT hai d j) x hx).trans
      (mul_le_mul_of_nonneg_left (localError_norm p a center ha i R T k hKR hT d j) hC)

end OQ14.ConicalCommonErrorNorm
#print axioms OQ14.ConicalCommonErrorNorm.localError_norm
#print axioms OQ14.ConicalCommonErrorNorm.localError_ae
#print axioms OQ14.ConicalCommonErrorNorm.localError_ae_closed
#print axioms OQ14.ConicalCommonErrorNorm.uniform_error_bound
