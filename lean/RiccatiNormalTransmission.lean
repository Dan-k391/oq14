import RiccatiTransmission

/-! Exact normal displacement and magnetic matching for the Riccati fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.RiccatiNormalTransmission
open Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.RiccatiTransmission
  OQ14.RiccatiDebyeTrace OQ14.DebyeRadialTrace

def NormalMatch (ε ζ : ℂ) (E H E' H' : Field) (R : ℝ) : Prop :=
  ∀ x : Space, ‖x‖=R → dot (position x) (ε • E x)=dot (position x) (ζ • E' x) ∧
    dot (position x) (H x)=dot (position x) (H' x)

theorem dot_scale (v w : Vector) (c : ℂ) : dot v (c • w)=c*dot v w := by
  simp only [dot,Pi.smul_apply,smul_eq_mul]
  ring

theorem te_matches (l : ℕ) (k ε ζ : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l v) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (R : ℝ) (hR : 0 < R) (hval : u R=v R) :
    NormalMatch ε ζ (teE l u p) (teH l k u p) (teE l v p) (teH l k v p) R := by
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
  constructor
  · change dot (position x) (ε • M l u p x)=dot (position x) (ζ • M l v p x)
    simp only [dot_scale,M_radial l u hu p x hx0,M_radial l v hv p x hx0,mul_zero]
  · change dot (position x) ((-Complex.I/k) • N l u p x)=
      dot (position x) ((-Complex.I/k) • N l v p x)
    rw [dot_scale,dot_scale,N_radial l u hu p hp hh x hx0,N_radial l v hv p hp hh x hx0,hx,hval]

theorem tm_matches (l : ℕ) (k ε ζ : ℂ) (hε : ε ≠ 0) (hζ : ζ ≠ 0) (u v : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l v) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (R : ℝ) (hR : 0 < R) (hval : u R=v R) :
    NormalMatch ε ζ (tmE l ε u p) (tmH l k u p) (tmE l ζ v p) (tmH l k v p) R := by
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
  constructor
  · change dot (position x) (ε • (ε⁻¹ • N l u p x))=
      dot (position x) (ζ • (ζ⁻¹ • N l v p x))
    rw [smul_smul,smul_smul,mul_inv_cancel₀ hε,mul_inv_cancel₀ hζ,one_smul,one_smul,
      N_radial l u hu p hp hh x hx0,N_radial l v hv p hp hh x hx0,hx,hval]
  · change dot (position x) ((-Complex.I*k) • M l u p x)=
      dot (position x) ((-Complex.I*k) • M l v p x)
    simp only [dot_scale,M_radial l u hu p x hx0,M_radial l v hv p x hx0,mul_zero]

end OQ14.RiccatiNormalTransmission

#print axioms OQ14.RiccatiNormalTransmission.dot_scale
#print axioms OQ14.RiccatiNormalTransmission.te_matches
#print axioms OQ14.RiccatiNormalTransmission.tm_matches
