import RiccatiDebyeTrace

/-! Actual spherical tangential matching for both Riccati Maxwell polarizations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.RiccatiTransmission
open Set OQ14.Maxwell OQ14.DebyeRadialTrace OQ14.RiccatiDebyeTrace OQ14.HarmonicPolynomial

def teE (l : ℕ) (u : ℝ → ℂ) (p : Poly) : Field := M l u p
def teH (l : ℕ) (k : ℂ) (u : ℝ → ℂ) (p : Poly) : Field := fun x => (-Complex.I/k) • N l u p x
def tmE (l : ℕ) (ε : ℂ) (u : ℝ → ℂ) (p : Poly) : Field := fun x => ε⁻¹ • N l u p x
def tmH (l : ℕ) (k : ℂ) (u : ℝ → ℂ) (p : Poly) : Field := fun x => (-Complex.I*k) • M l u p x

def TangentialMatch (E H E' H' : Field) (R : ℝ) : Prop :=
  ∀ x : Space, ‖x‖=R → crossProduct (position x) (E x)=crossProduct (position x) (E' x) ∧
    crossProduct (position x) (H x)=crossProduct (position x) (H' x)

theorem cross_scale (x : Space) (c : ℂ) (v : Vector) :
    crossProduct (position x) (c • v)=c • crossProduct (position x) v :=
  (crossProduct (position x)).map_smul c v

theorem te_matches (l : ℕ) (k : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l v) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (R : ℝ) (hR : 0 < R) (uD vD : ℂ) (hud : HasDerivAt u uD R) (hvd : HasDerivAt v vD R)
    (hval : u R=v R) (hmom : uD=vD) :
    TangentialMatch (teE l u p) (teH l k u p) (teE l v p) (teH l k v p) R := by
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
  have hud' : HasDerivAt u uD ‖x‖ := hx ▸ hud
  have hvd' : HasDerivAt v vD ‖x‖ := hx ▸ hvd
  constructor
  · ext i
    change crossProduct (position x) (M l u p x) i=crossProduct (position x) (M l v p x) i
    rw [M_cross l u hu p hp x hx0,M_cross l v hv p hp x hx0,hx,hval]
  · change crossProduct (position x) ((-Complex.I/k) • N l u p x)=
        crossProduct (position x) ((-Complex.I/k) • N l v p x)
    rw [cross_scale,cross_scale]
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,N_cross l u hu p hp hh x hx0 uD hud',
      N_cross l v hv p hp hh x hx0 vD hvd',hmom]

theorem tm_matches (l : ℕ) (k ε ζ : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l u) (Ioi 0))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l v) (Ioi 0))
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (R : ℝ) (hR : 0 < R) (uD vD : ℂ) (hud : HasDerivAt u uD R) (hvd : HasDerivAt v vD R)
    (hval : u R=v R) (hmom : uD/ε=vD/ζ) :
    TangentialMatch (tmE l ε u p) (tmH l k u p) (tmE l ζ v p) (tmH l k v p) R := by
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
  have hud' : HasDerivAt u uD ‖x‖ := hx ▸ hud
  have hvd' : HasDerivAt v vD ‖x‖ := hx ▸ hvd
  constructor
  · change crossProduct (position x) (ε⁻¹ • N l u p x)=crossProduct (position x) (ζ⁻¹ • N l v p x)
    rw [cross_scale,cross_scale]
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,N_cross l u hu p hp hh x hx0 uD hud',
      N_cross l v hv p hp hh x hx0 vD hvd']
    calc
      _ = -(uD/ε)/(‖x‖ : ℂ)^l*angularToroidal p x i := by ring
      _ = -(vD/ζ)/(‖x‖ : ℂ)^l*angularToroidal p x i := by rw [hmom]
      _ = _ := by ring
  · change crossProduct (position x) ((-Complex.I*k) • M l u p x)=
        crossProduct (position x) ((-Complex.I*k) • M l v p x)
    rw [cross_scale,cross_scale]
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,M_cross l u hu p hp x hx0,
      M_cross l v hv p hp x hx0,hx,hval]

end OQ14.RiccatiTransmission

#print axioms OQ14.RiccatiTransmission.cross_scale
#print axioms OQ14.RiccatiTransmission.te_matches
#print axioms OQ14.RiccatiTransmission.tm_matches
