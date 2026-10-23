import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Genuine polynomial-exponential packets belong to distinct generalized derivative eigenspaces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EntireExponentialPackets

def smoothFunctions : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContDiff ℂ (⊤ : ℕ∞) f}
  zero_mem' := by change ContDiff ℂ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℂ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℂ (⊤ : ℕ∞) f at hf
    change ContDiff ℂ (⊤ : ℕ∞) g at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℂ (⊤ : ℕ∞) f at hf
    exact hf.const_smul c

abbrev Entire := smoothFunctions

def derivative : Module.End ℂ Entire where
  toFun f := ⟨deriv (f : ℂ → ℂ),(contDiff_infty_iff_deriv.mp (show ContDiff ℂ (⊤ : ℕ∞) (f : ℂ → ℂ) from f.property)).2⟩
  map_add' f g := by
    apply Subtype.ext
    funext z
    have hf : ContDiff ℂ (⊤ : ℕ∞) (f : ℂ → ℂ) := f.property
    have hg : ContDiff ℂ (⊤ : ℕ∞) (g : ℂ → ℂ) := g.property
    change deriv ((f : ℂ → ℂ)+(g : ℂ → ℂ)) z=deriv (f : ℂ → ℂ) z+deriv (g : ℂ → ℂ) z
    exact deriv_add (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)
  map_smul' c f := by
    apply Subtype.ext
    funext z
    have hf : ContDiff ℂ (⊤ : ℕ∞) (f : ℂ → ℂ) := f.property
    change deriv (fun z => c*(f : ℂ → ℂ) z) z=c*deriv (f : ℂ → ℂ) z
    exact deriv_const_mul c (hf.differentiable (by simp) z)

def packet (ζ a b c : ℂ) : Entire :=
  ⟨fun z => (a+b*z+c*z^2)*Complex.exp (ζ*z),by
    change ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => (a+b*z+c*z^2)*Complex.exp (ζ*z))
    exact ((contDiff_const.add (contDiff_const.mul contDiff_id)).add
      (contDiff_const.mul (contDiff_id.pow 2))).mul ((contDiff_const.mul contDiff_id).cexp)⟩

theorem shift_packet (ζ a b c : ℂ) :
    (derivative-ζ • (1 : Module.End ℂ Entire)) (packet ζ a b c)=packet ζ b (2*c) 0 := by
  apply Subtype.ext
  funext z
  have hp : HasDerivAt (fun w : ℂ => a+b*w+c*w^2) (b+2*c*z) z := by
    convert ((hasDerivAt_const z a).add ((hasDerivAt_id z).const_mul b)).add
      (((hasDerivAt_id z).pow 2).const_mul c) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have he : HasDerivAt (fun w : ℂ => Complex.exp (ζ*w)) (Complex.exp (ζ*z)*ζ) z := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id z).const_mul ζ).cexp)
  change deriv (fun w => (a+b*w+c*w^2)*Complex.exp (ζ*w)) z-
    ζ*((a+b*z+c*z^2)*Complex.exp (ζ*z))=(b+(2*c)*z+0*z^2)*Complex.exp (ζ*z)
  rw [(hp.mul he).deriv]
  ring

theorem packet_generalized (ζ a b c : ℂ) : packet ζ a b c ∈ derivative.genEigenspace ζ (3 : ℕ) := by
  rw [Module.End.mem_genEigenspace_nat,LinearMap.mem_ker]
  norm_num only [pow_succ,Module.End.mul_apply,pow_zero,Module.End.one_apply,shift_packet,mul_zero]
  apply Subtype.ext
  funext z
  simp [packet]

theorem packet_zero (ζ a b c : ℂ) (h : packet ζ a b c=0) : a=0 ∧ b=0 ∧ c=0 := by
  have hp (z : ℂ) : a+b*z+c*z^2=0 := by
    have he := congrArg (fun f : Entire => (f : ℂ → ℂ) z) h
    change (a+b*z+c*z^2)*Complex.exp (ζ*z)=0 at he
    exact (mul_eq_zero.mp he).resolve_right (Complex.exp_ne_zero _)
  have h0 := hp 0
  have h1 := hp 1
  have hm := hp (-1)
  norm_num at h0 h1 hm
  refine ⟨h0,?_,?_⟩
  · linear_combination (1/2 : ℂ)*h1-(1/2 : ℂ)*hm
  · linear_combination (1/2 : ℂ)*h1+(1/2 : ℂ)*hm-h0

theorem distinct_packets {ι : Type*} [Fintype ι] (ζ a b c : ι → ℂ) (hζ : Function.Injective ζ)
    (h : ∀ z : ℂ, ∑ i, (a i+b i*z+c i*z^2)*Complex.exp (ζ i*z)=0) :
    ∀ i, a i=0 ∧ b i=0 ∧ c i=0 := by
  classical
  have hs : (∑ i, packet (ζ i) (a i) (b i) (c i))=0 := by
    apply Subtype.ext
    funext z
    simpa only [Submodule.coe_sum,Finset.sum_apply,packet,ZeroMemClass.coe_zero,Pi.zero_apply] using h z
  have hi := (derivative.independent_genEigenspace (3 : ℕ)).comp hζ
  intro i
  apply packet_zero
  have hother : (∑ j ∈ Finset.univ.erase i, packet (ζ j) (a j) (b j) (c j)) ∈
      ⨆ j, ⨆ (_ : j ≠ i), derivative.genEigenspace (ζ j) (3 : ℕ) := by
    apply Submodule.sum_mem
    intro j hj
    have hle : derivative.genEigenspace (ζ j) (3 : ℕ) ≤
        ⨆ n, ⨆ (_ : n ≠ i), derivative.genEigenspace (ζ n) (3 : ℕ) :=
      le_iSup_of_le j (le_iSup_of_le (Finset.ne_of_mem_erase hj) le_rfl)
    exact hle (packet_generalized (ζ j) (a j) (b j) (c j))
  have hsum := Finset.sum_erase_add Finset.univ (fun j => packet (ζ j) (a j) (b j) (c j)) (Finset.mem_univ i)
  rw [hs] at hsum
  have heq : packet (ζ i) (a i) (b i) (c i)= -∑ j ∈ Finset.univ.erase i, packet (ζ j) (a j) (b j) (c j) :=
    eq_neg_of_add_eq_zero_right hsum
  apply Submodule.disjoint_def.mp (hi i) _ (packet_generalized _ _ _ _)
  rw [heq]
  exact Submodule.neg_mem _ hother

end OQ14.EntireExponentialPackets
#print axioms OQ14.EntireExponentialPackets.shift_packet
#print axioms OQ14.EntireExponentialPackets.packet_generalized
#print axioms OQ14.EntireExponentialPackets.packet_zero
#print axioms OQ14.EntireExponentialPackets.distinct_packets
