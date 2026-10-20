import ModalFieldPole
import ModalHCurl

/-! # The actual shell-response residue is a global outgoing weak mode

The very same residue amplitudes define regular interior and outgoing
exterior fields satisfying the assembled Maxwell equations. The shell
restriction of this global mode is the actual response residue. This does
not identify the full Maxwell resolvent or exclude other angular degrees.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalPoleMode

open Complex MeasureTheory Metric Filter OQ14.Maxwell OQ14.ModalMatching
  OQ14.ModalAlgebra OQ14.ModalProfiles OQ14.ModalWeak OQ14.ModalLocal
  OQ14.ModalInterface OQ14.ModalShell OQ14.ModalFieldResidue OQ14.ModalFieldPole
open scoped Topology

def electricMode (n k : ℂ) (f : Amplitudes) : Field :=
  electric n k (residue 1 n k f).1 (residue 1 n k f).2

def magneticMode (n k : ℂ) (f : Amplitudes) : Field :=
  magnetic n k (residue 1 n k f).1 (residue 1 n k f).2

theorem residue_matching (n k : ℂ) (hd : tmDet 1 n k = 0) (f : Amplitudes) :
    matching 1 n k ((residue 1 n k f).1, (residue 1 n k f).2) = 0 :=
  residue_in_matching_kernel 1 n k hd f

theorem residue_weak_maxwell (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hd : tmDet 1 n k = 0) (f : Amplitudes)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (electricMode n k f) φ =
      (fun j => ∫ x, (I*k*magneticMode n k f x j)*φ x) ∧
    weakCurlPairing (magneticMode n k f) φ =
      (fun j => ∫ x, (-I*k*coefficient n x*electricMode n k f x j)*φ x) :=
  assembled_weak_maxwell n k _ _ hn hk (residue_matching n k hd f) φ hφ hc

theorem residue_local_L2 (n k : ℂ) (hk : k ≠ 0) (f : Amplitudes)
    (Ω : Set Space) (hΩ : Bornology.IsBounded Ω) (j : Fin 3) :
    MemLp (fun x => electricMode n k f x j) 2 (volume.restrict Ω) ∧
      MemLp (fun x => magneticMode n k f x j) 2 (volume.restrict Ω) :=
  ⟨electric_memLp_bounded n k _ _ hk Ω hΩ 2 j,
    magnetic_memLp_bounded n k _ _ hk Ω hΩ 2 j⟩

theorem residue_exterior (n k : ℂ) (f : Amplitudes) (x : Space) (hx : 1 < ‖x‖) :
    electricMode n k f x = outerE k (residue 1 n k f).2 x ∧
      magneticMode n k f x = outerH k (residue 1 n k f).2 x :=
  assembled_exterior n k _ _ x hx

theorem ae_shell_exterior : ∀ᵐ (x : Shell) ∂shellMeasure, 1 < ‖(x : Space)‖ := by
  have ha : ∀ᵐ x ∂(volume.restrict shell), ‖x‖ ≠ (1 : ℝ) :=
    ae_restrict_of_ae ((OQ14.RadialInterface.ae_regular 1).mono fun _ hx => hx.2)
  have hb : ∀ᵐ (x : Shell) ∂shellMeasure, ‖(x : Space)‖ ≠ (1 : ℝ) :=
    (ae_restrict_iff_subtype shell_compact.measurableSet).mp ha
  filter_upwards [hb] with x hx
  exact lt_of_le_of_ne x.property.1 hx.symm

theorem residue_shell_actual (n : ℂ) (k : Frequency) (f : Amplitudes) :
    (residueOperator n k f : Shell → PairVector) =ᵐ[shellMeasure] fun x =>
      (electricMode n k.1 f x.1, magneticMode n k.1 f x.1) := by
  filter_upwards [residueOperator_actual n k f, ae_shell_exterior] with x hx he
  rw [hx, (residue_exterior n k.1 f x.1 he).1, (residue_exterior n k.1 f x.1 he).2]

theorem residue_nontrivial (n : ℂ) (k : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k.1 = 0) (hs : deriv (tmDet 1 n) k.1 ≠ 0) :
    ∃ f : Amplitudes, (residue 1 n k.1 f).1 ≠ 0 ∧
      (residue 1 n k.1 f).2 ≠ 0 ∧ residueOperator n k f ≠ 0 := by
  obtain ⟨f,hf⟩ := residue_nonzero 1 n k.1 k.property hs
  have ha := matching_nonzero_amplitudes 1 n k.1 hn k.property _
    hf (residue_in_matching_kernel 1 n k.1 hd f)
  refine ⟨f,ha.1,ha.2,?_⟩
  rw [residueOperator_apply]
  exact smul_ne_zero ha.2 (unitL2_ne_zero k)

theorem residue_regional_graphs (n : ℂ) (k : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k.1 = 0) (f : Amplitudes)
    (hb : (residue 1 n k.1 f).2 ≠ 0) :
    ∃ E H : DomainCurl.HCurl (ball 0 2), (E ≠ 0 ∨ H ≠ 0) ∧
      (∀ᵐ x ∂DomainCurl.regionMeasure (ball 0 2), ∀ j : Fin 3,
        E.val.1 j x = electricMode n k.1 f x j ∧
        H.val.1 j x = magneticMode n k.1 f x j) ∧
      (∀ᵐ x ∂DomainCurl.regionMeasure (ball 0 2), ∀ j : Fin 3,
        E.val.2 j x = I*k.1*H.val.1 j x ∧
        H.val.2 j x = -I*k.1*coefficient n x*E.val.1 j x) := by
  let a := (residue 1 n k.1 f).1
  let b := (residue 1 n k.1 f).2
  have hm := residue_matching n k.1 hd f
  refine ⟨ModalHCurl.electricGraph n k.1 a b hn k.property hm
      (ball 0 2) isOpen_ball isBounded_ball,
    ModalHCurl.magneticGraph n k.1 a b hn k.property hm
      (ball 0 2) isOpen_ball isBounded_ball,
    ModalHCurl.graphs_not_both_zero n k.1 a b hn k.property hb hm, ?_,
    ModalHCurl.graph_maxwell_ae n k.1 a b hn k.property hm
      (ball 0 2) isOpen_ball isBounded_ball⟩
  apply ae_all_iff.mpr
  intro j
  filter_upwards [ModalHCurl.electricGraph_field_ae n k.1 a b hn k.property hm
      (ball 0 2) isOpen_ball isBounded_ball j,
    ModalHCurl.magneticGraph_field_ae n k.1 a b hn k.property hm
      (ball 0 2) isOpen_ball isBounded_ball j] with x he hh
  exact ⟨he,hh⟩

/-- The same frequency is an actual order-minus-one shell response pole and
supports its actual nonzero residue mode with global weak Maxwell equations.
The material coefficient is the ordinary positive dielectric sphere when
`n` is real and greater than one. -/
theorem exists_high_quality_residue_modes (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : Frequency, ∃ f : Amplitudes,
      L < k.1.re ∧ k.1.im < 0 ∧ Q < k.1.re / (-2*k.1.im) ∧
      (∃ hm : MeromorphicAt (response (n : ℂ)) k.1, hm.order = (-1 : ℤ)) ∧
      residueOperator (n : ℂ) k f ≠ 0 ∧
      ((residueOperator (n : ℂ) k f : Shell → PairVector) =ᵐ[shellMeasure] fun x =>
        (electricMode (n : ℂ) k.1 f x.1, magneticMode (n : ℂ) k.1 f x.1)) ∧
      (∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        weakCurlPairing (electricMode (n : ℂ) k.1 f) φ =
          (fun j => ∫ x, (I*k.1*magneticMode (n : ℂ) k.1 f x j)*φ x) ∧
        weakCurlPairing (magneticMode (n : ℂ) k.1 f) φ =
          (fun j => ∫ x, (-I*k.1*coefficient (n : ℂ) x*
            electricMode (n : ℂ) k.1 f x j)*φ x)) := by
  obtain ⟨k, hk, hd, hs, hL, hi, hratio⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros 1 n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  obtain ⟨f,_,_,hf⟩ := residue_nontrivial (n : ℂ) ⟨k,hk⟩ hn0 hd hs
  exact ⟨⟨k,hk⟩,f,hL,hi,hratio,
    ⟨response_meromorphic (n : ℂ) k hn0 hk,
      response_order_minus_one (n : ℂ) ⟨k,hk⟩ hn0 hd hs⟩,
    hf, residue_shell_actual (n : ℂ) ⟨k,hk⟩ f, residue_weak_maxwell (n : ℂ) k hn0 hk hd f⟩

end OQ14.ModalPoleMode


#print axioms OQ14.ModalPoleMode.residue_matching
#print axioms OQ14.ModalPoleMode.residue_weak_maxwell
#print axioms OQ14.ModalPoleMode.residue_local_L2
#print axioms OQ14.ModalPoleMode.residue_exterior
#print axioms OQ14.ModalPoleMode.ae_shell_exterior
#print axioms OQ14.ModalPoleMode.residue_shell_actual
#print axioms OQ14.ModalPoleMode.residue_nontrivial
#print axioms OQ14.ModalPoleMode.residue_regional_graphs
#print axioms OQ14.ModalPoleMode.exists_high_quality_residue_modes
