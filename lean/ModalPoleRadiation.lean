import ModalPoleMode
import ModalOutgoing

/-! # The same actual pole residue satisfies the outgoing condition

The complex-frequency exponential weight and actual normal cross product
are retained. The result concerns the constructed spherical matching
response and its global weak mode, not the full Maxwell resolvent.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalPoleRadiation

open Complex MeasureTheory Filter OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching
  OQ14.ModalProfiles OQ14.ModalWeak OQ14.ModalInterface OQ14.ModalShell
  OQ14.ModalFieldResidue OQ14.ModalFieldPole OQ14.ModalPoleMode OQ14.ModalOutgoing
open scoped Topology

def modeRadiationDefect (n k : ℂ) (f : Amplitudes) (x : Space) : Vector :=
  (Complex.exp (-I*k*‖x‖)*(‖x‖ : ℂ)) •
    (magneticMode n k f x - ((‖x‖ : ℂ)⁻¹) • tangent x (electricMode n k f x))

theorem modeRadiationDefect_exterior (n k : ℂ) (f : Amplitudes)
    (x : Space) (hx : 1 < ‖x‖) :
    modeRadiationDefect n k f x =
      spatialRadiationDefect k (residue 1 n k f).2 x := by
  simp only [modeRadiationDefect, spatialRadiationDefect,
    (residue_exterior n k f x hx).1, (residue_exterior n k f x hx).2]

theorem modeRadiationDefect_bound (n k : ℂ) (hk : k ≠ 0) (f : Amplitudes)
    (x : Space) (hx : 1 < ‖x‖) :
    ‖modeRadiationDefect n k f x‖ ≤ ‖(residue 1 n k f).2‖ / (‖k‖ * ‖x‖^2) := by
  rw [modeRadiationDefect_exterior n k f x hx]
  exact spatialRadiationDefect_bound k _ hk x (norm_pos_iff.mp (lt_trans zero_lt_one hx))

theorem modeRadiationDefect_limit (n k : ℂ) (hk : k ≠ 0) (f : Amplitudes)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => modeRadiationDefect n k f (γ t)) atTop (𝓝 0) := by
  apply (spatialRadiationDefect_limit k (residue 1 n k f).2 hk γ hγ).congr'
  filter_upwards [hγ.eventually (eventually_gt_atTop (1 : ℝ))] with t ht
  exact (modeRadiationDefect_exterior n k f (γ t) ht).symm

theorem mode_electric_far_limit (n k : ℂ) (hk : k ≠ 0) (f : Amplitudes)
    (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => (Complex.exp (-I*k*r)*(r : ℂ)) • electricMode n k f (r • d))
      atTop (𝓝 (electricFar k (residue 1 n k f).2 d)) := by
  apply (electric_far_limit k (residue 1 n k f).2 hk d hd).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hx : 1 < ‖r • d‖ := by rw [ray_norm r (lt_trans zero_lt_one hr) d hd]; exact hr
  rw [(residue_exterior n k f (r • d) hx).1]
  rfl

theorem mode_magnetic_far_limit (n k : ℂ) (hk : k ≠ 0) (f : Amplitudes)
    (d : Space) (hd : ‖d‖ = 1) :
    Tendsto (fun r : ℝ => (Complex.exp (-I*k*r)*(r : ℂ)) • magneticMode n k f (r • d))
      atTop (𝓝 (magneticFar k (residue 1 n k f).2 d)) := by
  apply (magnetic_far_limit k (residue 1 n k f).2 hk d hd).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hx : 1 < ‖r • d‖ := by rw [ray_norm r (lt_trans zero_lt_one hr) d hd]; exact hr
  rw [(residue_exterior n k f (r • d) hx).2]
  rfl

theorem nonzero_residue_far_field (n : ℂ) (k : Frequency) (f : Amplitudes)
    (hf : residueOperator n k f ≠ 0) :
    ∃ d : Space, ‖d‖ = 1 ∧ electricFar k.1 (residue 1 n k.1 f).2 d ≠ 0 ∧
      magneticFar k.1 (residue 1 n k.1 f).2 d ≠ 0 := by
  have hb : (residue 1 n k.1 f).2 ≠ 0 := by
    intro h
    exact hf (by rw [residueOperator_apply, h, zero_smul])
  exact far_field_nonzero k.1 _ k.property hb

/-- A single frequency and a single residue input give the actual simple
shell-response pole, a nonzero global weak Maxwell mode, and the explicit
outgoing condition along every path to infinity. -/
theorem exists_high_quality_radiating_residue_modes (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : Frequency, ∃ f : Amplitudes,
      L < k.1.re ∧ k.1.im < 0 ∧ Q < k.1.re / (-2*k.1.im) ∧
      (∃ hm : MeromorphicAt (response (n : ℂ)) k.1, hm.order = (-1 : ℤ)) ∧
      residueOperator (n : ℂ) k f ≠ 0 ∧
      (∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
        weakCurlPairing (electricMode (n : ℂ) k.1 f) φ =
          (fun j => ∫ x, (I*k.1*magneticMode (n : ℂ) k.1 f x j)*φ x) ∧
        weakCurlPairing (magneticMode (n : ℂ) k.1 f) φ =
          (fun j => ∫ x, (-I*k.1*coefficient (n : ℂ) x*
            electricMode (n : ℂ) k.1 f x j)*φ x)) ∧
      (∀ (γ : ℝ → Space), Tendsto (fun t => ‖γ t‖) atTop atTop →
        Tendsto (fun t => modeRadiationDefect (n : ℂ) k.1 f (γ t)) atTop (𝓝 0)) ∧
      (∃ d : Space, ‖d‖ = 1 ∧ electricFar k.1 (residue 1 (n : ℂ) k.1 f).2 d ≠ 0 ∧
        magneticFar k.1 (residue 1 (n : ℂ) k.1 f).2 d ≠ 0) := by
  obtain ⟨k,f,hL,hi,hQk,hpole,hf,_,hweak⟩ :=
    exists_high_quality_residue_modes n hn L Q hQ
  exact ⟨k,f,hL,hi,hQk,hpole,hf,hweak,
    modeRadiationDefect_limit (n : ℂ) k.1 k.property f,
    nonzero_residue_far_field (n : ℂ) k f hf⟩

end OQ14.ModalPoleRadiation

#print axioms OQ14.ModalPoleRadiation.modeRadiationDefect_exterior
#print axioms OQ14.ModalPoleRadiation.modeRadiationDefect_bound
#print axioms OQ14.ModalPoleRadiation.modeRadiationDefect_limit
#print axioms OQ14.ModalPoleRadiation.mode_electric_far_limit
#print axioms OQ14.ModalPoleRadiation.mode_magnetic_far_limit
#print axioms OQ14.ModalPoleRadiation.nonzero_residue_far_field
#print axioms OQ14.ModalPoleRadiation.exists_high_quality_radiating_residue_modes
