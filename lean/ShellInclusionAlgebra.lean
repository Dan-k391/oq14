import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-! Exact elimination of a shell block in a weighted volume operator, in an arbitrary ring:
push-through inverses, the effective inclusion operator, and the explicit inverse of the
combined block. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ShellInclusionAlgebra

variable {R : Type*} [Ring R]

theorem mul_eq_sub_one_of_left {x r : R} (h : (1-x)*r=1) : x*r=r-1 := by
  rw [sub_mul,one_mul,sub_eq_iff_eq_add] at h
  rw [eq_sub_iff_add_eq,add_comm]
  exact h.symm

theorem mul_eq_sub_one_of_right {x r : R} (h : r*(1-x)=1) : r*x=r-1 := by
  rw [mul_sub,mul_one,sub_eq_iff_eq_add] at h
  rw [eq_sub_iff_add_eq,add_comm]
  exact h.symm

theorem one_sub_mul_mul_pushThrough (a b r : R) (hr : (1-b*a)*r=1) :
    (1-a*b)*(1+a*r*b)=1 := by
  have h2 : b*a*r=r-1 := mul_eq_sub_one_of_left hr
  calc (1-a*b)*(1+a*r*b)=1+a*r*b-a*b-a*(b*a*r)*b := by noncomm_ring
    _ = 1 := by rw [h2]; noncomm_ring

theorem pushThrough_mul_one_sub_mul (a b r : R) (hr : r*(1-b*a)=1) :
    (1+a*r*b)*(1-a*b)=1 := by
  have h2 : r*(b*a)=r-1 := mul_eq_sub_one_of_right hr
  calc (1+a*r*b)*(1-a*b)=1-a*b+a*r*b-a*(r*(b*a))*b := by noncomm_ring
    _ = 1 := by rw [h2]; noncomm_ring

theorem isUnit_one_sub_mul_swap (a b : R) (h : IsUnit (1-b*a)) : IsUnit (1-a*b) :=
  ⟨⟨1-a*b,1+a*Ring.inverse (1-b*a)*b,
    one_sub_mul_mul_pushThrough a b _ (Ring.mul_inverse_cancel _ h),
    pushThrough_mul_one_sub_mul a b _ (Ring.inverse_mul_cancel _ h)⟩,rfl⟩

theorem inverse_one_sub_mul_swap (a b : R) (h : IsUnit (1-b*a)) :
    Ring.inverse (1-a*b)=1+a*Ring.inverse (1-b*a)*b := by
  let u : Rˣ := ⟨1-a*b,1+a*Ring.inverse (1-b*a)*b,
    one_sub_mul_mul_pushThrough a b _ (Ring.mul_inverse_cancel _ h),
    pushThrough_mul_one_sub_mul a b _ (Ring.inverse_mul_cancel _ h)⟩
  exact Ring.inverse_unit u

/-- Left push-through identity of the shell Green element `G = T + T Ss r Ss T`. -/
theorem green_left (Ss T r G : R) (hr1 : (1-Ss*T*Ss)*r=1) (hG : G=T+T*Ss*r*Ss*T) :
    (1-T*(Ss*Ss))*G=T := by
  have hA : Ss*T*Ss*r=r-1 := mul_eq_sub_one_of_left hr1
  subst hG
  calc (1-T*(Ss*Ss))*(T+T*Ss*r*Ss*T)=T+T*Ss*r*Ss*T-T*Ss*Ss*T-T*Ss*(Ss*T*Ss*r)*Ss*T := by noncomm_ring
    _ = T := by rw [hA]; noncomm_ring

/-- Right push-through identity of the shell Green element. -/
theorem green_right (Ss T r G : R) (hr2 : r*(1-Ss*T*Ss)=1) (hG : G=T+T*Ss*r*Ss*T) :
    G*(1-(Ss*Ss)*T)=T := by
  have hB : r*(Ss*T*Ss)=r-1 := mul_eq_sub_one_of_right hr2
  subst hG
  calc (T+T*Ss*r*Ss*T)*(1-(Ss*Ss)*T)=T+T*Ss*r*Ss*T-T*Ss*Ss*T-T*Ss*(r*(Ss*T*Ss))*Ss*T := by noncomm_ring
    _ = T := by rw [hB]; noncomm_ring

theorem sum_sq (Ss Si : R) (hsi : Ss*Si=0) (his : Si*Ss=0) : (Ss+Si)*(Ss+Si)=Ss*Ss+Si*Si := by
  calc (Ss+Si)*(Ss+Si)=Ss*Ss+Ss*Si+Si*Ss+Si*Si := by noncomm_ring
    _ = _ := by rw [hsi,his]; abel

theorem green_square (Ss Si T G : R) (hgr : G*(1-(Ss*Ss)*T)=T) (hsi : Ss*Si=0) (his : Si*Ss=0) :
    G*((Ss+Si)*(Ss+Si))*T=G-T+G*(Si*Si)*T := by
  rw [sum_sq Ss Si hsi his]
  have h1 : G*((Ss*Ss)*T)=G-T := by
    rw [mul_sub,mul_one,sub_eq_iff_eq_add] at hgr
    rw [eq_sub_iff_add_eq,add_comm]
    exact hgr.symm
  calc G*(Ss*Ss+Si*Si)*T=G*((Ss*Ss)*T)+G*(Si*Si)*T := by noncomm_ring
    _ = _ := by rw [h1]

/-- The effective inclusion equation follows from the combined equation:
`(1 - Si G Si) (Si T S) = (Si G S) (1 - S T S)` with `S = Ss + Si`. -/
theorem effective_of_combined (Ss Si T G : R) (hgr : G*(1-(Ss*Ss)*T)=T)
    (hsi : Ss*Si=0) (his : Si*Ss=0) :
    (1-Si*G*Si)*(Si*T*(Ss+Si))=(Si*G*(Ss+Si))*(1-(Ss+Si)*T*(Ss+Si)) := by
  have hGSS := green_square Ss Si T G hgr hsi his
  set S := Ss+Si with hS
  set P := G*(S*S)*T with hP
  have e1 : (Si*G*S)*(1-S*T*S)=Si*G*S-Si*P*S := by rw [hP]; noncomm_ring
  rw [e1,hGSS]
  noncomm_ring

/-- Explicit right inverse of the combined block through the effective inclusion inverse. -/
theorem combined_mul_inverse (Ss Si T G E' : R) (hgl : (1-T*(Ss*Ss))*G=T)
    (hsi : Ss*Si=0) (his : Si*Ss=0) (hE1 : (1-Si*G*Si)*E'=1) :
    (1-(Ss+Si)*T*(Ss+Si))*(1+(Ss+Si)*(G*(Ss+Si)+G*Si*E'*Si*G*(Ss+Si)))=1 := by
  have hE : Si*G*Si*E'=E'-1 := mul_eq_sub_one_of_left hE1
  set S := Ss+Si with hS
  set Y := G*S+G*Si*E'*Si*G*S with hY
  have hSS : S*S=Ss*Ss+Si*Si := sum_sq Ss Si hsi his
  have hY1 : (1-T*(Ss*Ss))*Y=T*S+T*Si*E'*Si*G*S := by
    calc (1-T*(Ss*Ss))*Y=(1-T*(Ss*Ss))*G*(S+Si*E'*Si*G*S) := by rw [hY]; noncomm_ring
      _ = T*(S+Si*E'*Si*G*S) := by rw [hgl]
      _ = _ := by noncomm_ring
  have hY2 : T*(Si*Si)*Y=T*Si*E'*Si*G*S := by
    calc T*(Si*Si)*Y=T*Si*(Si*G*S)+T*Si*(Si*G*Si*E')*(Si*G*S) := by rw [hY]; noncomm_ring
      _ = _ := by rw [hE]; noncomm_ring
  have hZ : Y-T*S-T*(S*S)*Y=0 := by
    calc Y-T*S-T*(S*S)*Y=(1-T*(Ss*Ss))*Y-T*(Si*Si)*Y-T*S := by rw [hSS]; noncomm_ring
      _ = 0 := by rw [hY1,hY2]; noncomm_ring
  calc (1-S*T*S)*(1+S*Y)=1+S*(Y-T*S-T*(S*S)*Y) := by noncomm_ring
    _ = 1 := by rw [hZ]; noncomm_ring

/-- Explicit left inverse of the combined block through the effective inclusion inverse. -/
theorem inverse_mul_combined (Ss Si T G E' : R) (hgr : G*(1-(Ss*Ss)*T)=T)
    (hsi : Ss*Si=0) (his : Si*Ss=0) (hE2 : E'*(1-Si*G*Si)=1) :
    (1+(Ss+Si)*(G*(Ss+Si)+G*Si*E'*Si*G*(Ss+Si)))*(1-(Ss+Si)*T*(Ss+Si))=1 := by
  have hE : E'*(Si*G*Si)=E'-1 := mul_eq_sub_one_of_right hE2
  have hGSS := green_square Ss Si T G hgr hsi his
  set S := Ss+Si with hS
  set Y := G*S+G*Si*E'*Si*G*S with hY
  set P := G*(S*S)*T with hP
  have e1 : Y*(S*T*S)=P*S+G*Si*E'*Si*P*S := by rw [hY,hP]; noncomm_ring
  have hW : Y-T*S-Y*(S*T*S)=0 := by
    rw [e1,hGSS,hY]
    calc G*S+G*Si*E'*Si*G*S-T*S-((G-T+G*(Si*Si)*T)*S+G*Si*E'*Si*(G-T+G*(Si*Si)*T)*S)=
        G*Si*(E'-E'*(Si*G*Si))*(Si*T*S)-G*Si*Si*T*S := by noncomm_ring
      _ = 0 := by rw [hE]; noncomm_ring
  calc (1+S*Y)*(1-S*T*S)=1+S*(Y-T*S-Y*(S*T*S)) := by noncomm_ring
    _ = 1 := by rw [hW]; noncomm_ring

/-- The shell Green element built from the ring inverse of the shell block. -/
def green (Ss T : R) : R := T+T*Ss*Ring.inverse (1-Ss*T*Ss)*Ss*T

theorem green_left_unit (Ss T : R) (hs : IsUnit (1-Ss*T*Ss)) : (1-T*(Ss*Ss))*green Ss T=T :=
  green_left Ss T _ _ (Ring.mul_inverse_cancel _ hs) rfl

theorem green_right_unit (Ss T : R) (hs : IsUnit (1-Ss*T*Ss)) : green Ss T*(1-(Ss*Ss)*T)=T :=
  green_right Ss T _ _ (Ring.inverse_mul_cancel _ hs) rfl

theorem effective_of_combined_unit (Ss Si T : R) (hs : IsUnit (1-Ss*T*Ss)) (hsi : Ss*Si=0) (his : Si*Ss=0) :
    (1-Si*green Ss T*Si)*(Si*T*(Ss+Si))=(Si*green Ss T*(Ss+Si))*(1-(Ss+Si)*T*(Ss+Si)) :=
  effective_of_combined Ss Si T _ (green_right_unit Ss T hs) hsi his

/-- If the shell block and the effective inclusion block are units, so is the combined block,
with the explicit inverse. -/
theorem combined_isUnit (Ss Si T : R) (hs : IsUnit (1-Ss*T*Ss)) (hsi : Ss*Si=0) (his : Si*Ss=0)
    (hE : IsUnit (1-Si*green Ss T*Si)) : IsUnit (1-(Ss+Si)*T*(Ss+Si)) :=
  ⟨⟨1-(Ss+Si)*T*(Ss+Si),
    1+(Ss+Si)*(green Ss T*(Ss+Si)+green Ss T*Si*Ring.inverse (1-Si*green Ss T*Si)*Si*green Ss T*(Ss+Si)),
    combined_mul_inverse Ss Si T _ _ (green_left_unit Ss T hs) hsi his (Ring.mul_inverse_cancel _ hE),
    inverse_mul_combined Ss Si T _ _ (green_right_unit Ss T hs) hsi his (Ring.inverse_mul_cancel _ hE)⟩,rfl⟩

theorem combined_inverse (Ss Si T : R) (hs : IsUnit (1-Ss*T*Ss)) (hsi : Ss*Si=0) (his : Si*Ss=0)
    (hE : IsUnit (1-Si*green Ss T*Si)) :
    Ring.inverse (1-(Ss+Si)*T*(Ss+Si))=
      1+(Ss+Si)*(green Ss T*(Ss+Si)+green Ss T*Si*Ring.inverse (1-Si*green Ss T*Si)*Si*green Ss T*(Ss+Si)) := by
  let u : Rˣ := ⟨1-(Ss+Si)*T*(Ss+Si),
    1+(Ss+Si)*(green Ss T*(Ss+Si)+green Ss T*Si*Ring.inverse (1-Si*green Ss T*Si)*Si*green Ss T*(Ss+Si)),
    combined_mul_inverse Ss Si T _ _ (green_left_unit Ss T hs) hsi his (Ring.mul_inverse_cancel _ hE),
    inverse_mul_combined Ss Si T _ _ (green_right_unit Ss T hs) hsi his (Ring.inverse_mul_cancel _ hE)⟩
  exact Ring.inverse_unit u

end OQ14.ShellInclusionAlgebra
#print axioms OQ14.ShellInclusionAlgebra.mul_eq_sub_one_of_left
#print axioms OQ14.ShellInclusionAlgebra.mul_eq_sub_one_of_right
#print axioms OQ14.ShellInclusionAlgebra.one_sub_mul_mul_pushThrough
#print axioms OQ14.ShellInclusionAlgebra.pushThrough_mul_one_sub_mul
#print axioms OQ14.ShellInclusionAlgebra.isUnit_one_sub_mul_swap
#print axioms OQ14.ShellInclusionAlgebra.inverse_one_sub_mul_swap
#print axioms OQ14.ShellInclusionAlgebra.green_left
#print axioms OQ14.ShellInclusionAlgebra.green_right
#print axioms OQ14.ShellInclusionAlgebra.sum_sq
#print axioms OQ14.ShellInclusionAlgebra.green_square
#print axioms OQ14.ShellInclusionAlgebra.effective_of_combined
#print axioms OQ14.ShellInclusionAlgebra.combined_mul_inverse
#print axioms OQ14.ShellInclusionAlgebra.inverse_mul_combined
#print axioms OQ14.ShellInclusionAlgebra.green_left_unit
#print axioms OQ14.ShellInclusionAlgebra.green_right_unit
#print axioms OQ14.ShellInclusionAlgebra.effective_of_combined_unit
#print axioms OQ14.ShellInclusionAlgebra.combined_isUnit
#print axioms OQ14.ShellInclusionAlgebra.combined_inverse
