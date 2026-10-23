import ForcedMaxwellResponse

/-! Actual outgoing forced Maxwell fields equal the compact-source volume response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.RadiatingSourceRepresentation
open MeasureTheory Metric Filter OQ14.Maxwell OQ14.ForcedMaxwellResponse OQ14.RadiatingTrace

theorem representative_memLp (k R T : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j) (i : Fin 3) :
    MemLp (fun x => ExteriorContinuity.representative k F ρ R x i) 2
      (volume.restrict (closedBall 0 T)) := by
  apply (LocalVolumeResponse.electric_memLp_ball k T R F ρ hρ hs hF i).ae_eq
  filter_upwards [ae_restrict_of_ae (ExteriorContinuity.representative_ae k F ρ hρ hF R hs)] with x hx
  exact (congrFun hx i).symm

theorem actual_response (k : ℝ) (hk : 0<k) (R : ℝ) (hR : 0≤R)
    (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestForced k ρ E H)
    (hEs : ∀ i x, R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => E z i) x)
    (t : Trace k E H) :
    (E =ᵐ[volume] FieldResponse.electric k F ρ) ∧
      (H =ᵐ[volume] MagneticResponse.magnetic k ρ) := by
  let G := ExteriorContinuity.representative k F ρ R
  let K := MagneticResponse.magnetic k ρ
  have hG (T : ℝ) (i : Fin 3) : MemLp (fun x => G x i) 2 (volume.restrict (closedBall 0 T)) :=
    representative_memLp k R T F ρ hρ hs hF i
  have hK (T : ℝ) (i : Fin 3) : MemLp (fun x => K x i) 2 (volume.restrict (closedBall 0 T)) :=
    MagneticLocal.magnetic_memLp_ball k T R F ρ hρ hs hF i
  have hlocal (V : Field)
      (hV : ∀ T i, MemLp (fun x => V x i) 2 (volume.restrict (closedBall 0 T))) (i : Fin 3) :
      LocallyIntegrable (fun x => V x i) :=
    HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => hV T i)
  have hdiff := difference_vacuum k ρ E H G K (hlocal E hE) (hlocal H hH)
    (hlocal G hG) (hlocal K hK) hMax (representative_forced k R F ρ hρ hs hF)
  obtain ⟨he,hh⟩ := vacuum_zero k hk R hR (E-G) (H-K)
    (fun T i => (hE T i).sub (hG T i)) (fun T i => (hH T i).sub (hK T i)) hdiff
    (fun i x hx => (hEs i x hx).sub (representative_smooth k R F ρ hρ hs i x hx))
    (t.sub (compactSource k R hR F ρ hρ hs))
  constructor
  · apply EventuallyEq.trans _ (ExteriorContinuity.representative_ae k F ρ hρ hF R hs)
    filter_upwards [he] with x hx
    exact sub_eq_zero.mp hx
  · filter_upwards [hh] with x hx
    exact sub_eq_zero.mp hx

end OQ14.RadiatingSourceRepresentation
#print axioms OQ14.RadiatingSourceRepresentation.representative_memLp
#print axioms OQ14.RadiatingSourceRepresentation.actual_response
