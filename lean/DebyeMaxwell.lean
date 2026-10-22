import DebyeCalculus

/-! Actual electric and magnetic Debye fields from local scalar Helmholtz solutions.
Both polarizations are verified with genuine Euclidean Frechet curls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.DebyeMaxwell
open OQ14.Maxwell OQ14.ExteriorClassical OQ14.ExteriorHelmholtz
  OQ14.ModalDipole OQ14.DebyeCalculus Complex

def teElectric (f : Space → ℂ) : Field := toroidal f
def teMagnetic (k : ℂ) (f : Space → ℂ) : Field := fun x j => -I/k*curl (toroidal f) x j
def tmElectric (f : Space → ℂ) : Field := curl (toroidal f)
def tmMagnetic (k ε : ℂ) (f : Space → ℂ) : Field := fun x j => -I*k*ε*toroidal f x j

theorem te_maxwell {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q k ε : ℂ) (hk : k ≠ 0)
    (hdisp : q^2=k^2*ε) (hHelm : ∀ y ∈ Ω, laplacian f y+q^2*f y=0)
    (x : Space) (hx : x ∈ Ω) :
    ComplexMaxwellAt k ε (teElectric f) (teMagnetic k f) x := by
  constructor
  · ext j
    dsimp [teElectric,teMagnetic]
    field_simp
    ring_nf
    simp [I_sq]
  · change curl (fun y j => (-I/k)*curl (toroidal f) y j) x = _
    rw [curl_const_mul _ x _ (fun j =>
      (curl_smooth _ (toroidal_smooth f x (hf x hx)) j).differentiableAt (by simp))]
    ext j
    rw [toroidal_curl_curl hΩ f hf q hHelm x hx, hdisp]
    dsimp [teElectric]
    field_simp
    ring

theorem tm_maxwell {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q k ε : ℂ)
    (hdisp : q^2=k^2*ε) (hHelm : ∀ y ∈ Ω, laplacian f y+q^2*f y=0)
    (x : Space) (hx : x ∈ Ω) :
    ComplexMaxwellAt k ε (tmElectric f) (tmMagnetic k ε f) x := by
  constructor
  · ext j
    change curl (curl (toroidal f)) x j = _
    rw [toroidal_curl_curl hΩ f hf q hHelm x hx, hdisp]
    dsimp [tmMagnetic]
    ring_nf
    simp [I_sq]
  · change curl (fun y j => (-I*k*ε)*toroidal f y j) x = _
    rw [curl_const_mul _ x _ (fun j =>
      (toroidal_smooth f x (hf x hx) j).differentiableAt (by simp))]
    rfl

theorem te_real_maxwell {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q k ε : ℝ) (hk : k ≠ 0)
    (hdisp : q^2=k^2*ε) (hHelm : ∀ y ∈ Ω, laplacian f y+(q : ℂ)^2*f y=0)
    (x : Space) (hx : x ∈ Ω) :
    MaxwellAt k 1 ε (teElectric f) (teMagnetic k f) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    te_maxwell hΩ f hf q k ε (Complex.ofReal_ne_zero.mpr hk) hd hHelm x hx

theorem tm_real_maxwell {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q k ε : ℝ)
    (hdisp : q^2=k^2*ε) (hHelm : ∀ y ∈ Ω, laplacian f y+(q : ℂ)^2*f y=0)
    (x : Space) (hx : x ∈ Ω) :
    MaxwellAt k 1 ε (tmElectric f) (tmMagnetic k ε f) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    tm_maxwell hΩ f hf q k ε hd hHelm x hx

end OQ14.DebyeMaxwell

#print axioms OQ14.DebyeMaxwell.te_maxwell
#print axioms OQ14.DebyeMaxwell.tm_maxwell
#print axioms OQ14.DebyeMaxwell.te_real_maxwell
#print axioms OQ14.DebyeMaxwell.tm_real_maxwell
