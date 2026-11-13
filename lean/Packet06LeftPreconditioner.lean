import Packet06SphereSchur

/-! Exact kernel, cokernel and simple-crossing transport under a fixed
invertible left preconditioner. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06LeftPreconditioner
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pencil (B A : E →L[ℂ] E) : E →L[ℂ] E := Ring.inverse B*A
def functional (B : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) : E →L[ℂ] ℂ := φ.comp B

theorem undo (B A : E →L[ℂ] E) (hB : IsUnit B) : B*pencil B A = A := by
  rw [pencil,←mul_assoc,Ring.mul_inverse_cancel _ hB,one_mul]

theorem kernel_iff (B A : E →L[ℂ] E) (hB : IsUnit B) (u : E) :
    pencil B A u = 0 ↔ A u = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun v : E => B v) h
    change (B*pencil B A) u = B 0 at hh
    simpa only [undo B A hB,map_zero] using hh
  · intro h
    change Ring.inverse B (A u) = 0
    rw [h,map_zero]

theorem pairing_undo (B A : E →L[ℂ] E) (hB : IsUnit B) (φ : E →L[ℂ] ℂ) (u : E) :
    functional B φ (pencil B A u) = φ (A u) := by
  change φ ((B*pencil B A) u) = _
  rw [undo B A hB]

theorem range_eq_kernel (B A : E →L[ℂ] E) (hB : IsUnit B) (φ : E →L[ℂ] ℂ)
    (hr : LinearMap.range A.toLinearMap = LinearMap.ker φ.toLinearMap) :
    LinearMap.range (pencil B A).toLinearMap = LinearMap.ker (functional B φ).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    change functional B φ (pencil B A x) = 0
    rw [pairing_undo B A hB]
    have hm : A x ∈ LinearMap.range A.toLinearMap := ⟨x,rfl⟩
    rw [hr] at hm
    exact hm
  · intro hy
    have hm : B y ∈ LinearMap.range A.toLinearMap := by
      rw [hr]
      exact hy
    obtain ⟨x,hx⟩ := hm
    refine ⟨x,?_⟩
    change Ring.inverse B (A x) = y
    change A x = B y at hx
    rw [hx]
    exact congrArg (fun L : E →L[ℂ] E => L y) (Ring.inverse_mul_cancel _ hB)

theorem hasDerivAt (B : E →L[ℂ] E) (A : ℂ → E →L[ℂ] E)
    (A₁ : E →L[ℂ] E) (z : ℂ) (hA : HasDerivAt A A₁ z) :
    HasDerivAt (fun v => pencil B (A v)) (pencil B A₁) z := by
  simpa only [zero_mul,zero_add] using (hasDerivAt_const z (Ring.inverse B)).mul hA

theorem crossing_preserved (B : E →L[ℂ] E) (hB : IsUnit B)
    (A : ℂ → E →L[ℂ] E) (A₁ : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) (u : E) (z : ℂ)
    (hA : HasDerivAt A A₁ z) :
    HasDerivAt (fun v => pencil B (A v)) (pencil B A₁) z ∧
      functional B φ (pencil B A₁ u) = φ (A₁ u) :=
  ⟨hasDerivAt B A A₁ z hA,pairing_undo B A₁ hB φ u⟩

end OQ14.Packet06LeftPreconditioner
#print axioms OQ14.Packet06LeftPreconditioner.undo
#print axioms OQ14.Packet06LeftPreconditioner.kernel_iff
#print axioms OQ14.Packet06LeftPreconditioner.pairing_undo
#print axioms OQ14.Packet06LeftPreconditioner.range_eq_kernel
#print axioms OQ14.Packet06LeftPreconditioner.hasDerivAt
#print axioms OQ14.Packet06LeftPreconditioner.crossing_preserved
