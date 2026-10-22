import RadialLayerMaxwell
import RiccatiNormalTransmission
import RadialStack

/-! Genuine spherical Maxwell transmission at adjacent explicit radial layers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RadialLayerTransmission
open Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.RadialStack OQ14.RadialLayer
  OQ14.RiccatiTransmission OQ14.RiccatiNormalTransmission

def FullMatch (ε ζ : ℂ) (E H E' H' : Field) (R : ℝ) : Prop :=
  TangentialMatch E H E' H' R ∧ NormalMatch ε ζ E H E' H' R

theorem wave_smooth (l : ℕ) (g : Layer) (s : State) :
    ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l (wave l g s)) (Ioi 0) :=
  RadialLayerMaxwell.profile_smooth l g.q g.σ _ _ g.q_pos.ne'

theorem wave_derivative (l : ℕ) (g : Layer) (s : State) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (wave l g s) ((g.σ : ℂ)*waveMomentum l g s r) r :=
  (solution_ode l g.q g.σ _ _ r g.q_pos.ne' g.σ_pos.ne' hr.ne').1

theorem adjacent_state (l : ℕ) (g h : Layer) (s : State) (hjoin : g.a=h.b) :
    wave l g s g.a=wave l h (back l g s) g.a ∧
      waveMomentum l g s g.a=waveMomentum l h (back l g s) g.a := by
  constructor
  · rw [(wave_inner l g s).1,hjoin,(wave_outer l h (back l g s)).1]
  · rw [(wave_inner l g s).2,hjoin,(wave_outer l h (back l g s)).2]

theorem te_adjacent (l : ℕ) (g h : Layer) (s : State) (hjoin : g.a=h.b)
    (hσg : g.σ=1) (hσh : h.σ=1) (k ε ζ : ℂ)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    FullMatch ε ζ (teE l (wave l g s) p) (teH l k (wave l g s) p)
      (teE l (wave l h (back l g s)) p) (teH l k (wave l h (back l g s)) p) g.a := by
  obtain ⟨hv,hm⟩ := adjacent_state l g h s hjoin
  constructor
  · apply RiccatiTransmission.te_matches l k _ _ (wave_smooth l g s) (wave_smooth l h (back l g s))
      p hp hh g.a g.a_pos _ _ (wave_derivative l g s g.a g.a_pos)
      (wave_derivative l h (back l g s) g.a g.a_pos) hv
    simpa only [hσg,hσh,Complex.ofReal_one,one_mul] using hm
  · exact RiccatiNormalTransmission.te_matches l k ε ζ _ _ (wave_smooth l g s)
      (wave_smooth l h (back l g s)) p hp hh g.a g.a_pos hv

theorem tm_adjacent (l : ℕ) (g h : Layer) (s : State) (hjoin : g.a=h.b) (k : ℂ)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    FullMatch g.σ h.σ (tmE l g.σ (wave l g s) p) (tmH l k (wave l g s) p)
      (tmE l h.σ (wave l h (back l g s)) p) (tmH l k (wave l h (back l g s)) p) g.a := by
  obtain ⟨hv,hm⟩ := adjacent_state l g h s hjoin
  have hσg : (g.σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr g.σ_pos.ne'
  have hσh : (h.σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.σ_pos.ne'
  constructor
  · apply RiccatiTransmission.tm_matches l k g.σ h.σ _ _ (wave_smooth l g s)
      (wave_smooth l h (back l g s)) p hp hh g.a g.a_pos _ _
      (wave_derivative l g s g.a g.a_pos) (wave_derivative l h (back l g s) g.a g.a_pos) hv
    simpa only [mul_div_cancel_left₀ _ hσg,mul_div_cancel_left₀ _ hσh] using hm
  · exact RiccatiNormalTransmission.tm_matches l k g.σ h.σ hσg hσh _ _ (wave_smooth l g s)
      (wave_smooth l h (back l g s)) p hp hh g.a g.a_pos hv

end OQ14.RadialLayerTransmission

#print axioms OQ14.RadialLayerTransmission.wave_smooth
#print axioms OQ14.RadialLayerTransmission.wave_derivative
#print axioms OQ14.RadialLayerTransmission.adjacent_state
#print axioms OQ14.RadialLayerTransmission.te_adjacent
#print axioms OQ14.RadialLayerTransmission.tm_adjacent
