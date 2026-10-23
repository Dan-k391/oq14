import SpatialReactionTerms
import DebyeMaxwell

/-! Actual compact derivative bounds for both regular vector Maxwell polarizations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DebyeJetBounds
open OQ14.Maxwell OQ14.ExteriorClassical OQ14.DebyeCalculus
  OQ14.SphereHarmonicBasis OQ14.HarmonicSpatialMajorant OQ14.SpatialReactionTerms
  OQ14.SpatialReactionMajorant OQ14.RiccatiSeriesCoefficients

theorem partial_jet_bound (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : ℕ) (x : Space) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => dcoord f y i) x‖ ≤
      ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const
    (c := Maxwell.basis i) (n := j) (x := x) (hf.contDiffAt.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
    (by exact_mod_cast le_top)
  simpa only [dcoord,norm_iteratedFDeriv_fderiv,show ‖Maxwell.basis i‖=(1 : ℝ) by simp [Maxwell.basis],one_mul] using h

theorem sub_jet_bound (f g : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ j (fun y => f y-g y) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖+‖iteratedFDeriv ℝ j g x‖ := by
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.neg.contDiffAt.of_le (by exact_mod_cast le_top))]
  change ‖iteratedFDeriv ℝ j f x+iteratedFDeriv ℝ j (-g) x‖≤_
  rw [iteratedFDeriv_neg_apply]
  simpa only [norm_neg] using norm_add_le (iteratedFDeriv ℝ j f x) (-iteratedFDeriv ℝ j g x)

theorem curl_jet_bound (F : Field) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x i))
    (j : ℕ) (x : Space) (A : ℝ)
    (hb : ∀ i, ‖iteratedFDeriv ℝ (j+1) (fun y => F y i) x‖ ≤ A) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => curl F y i) x‖ ≤ 2*A := by
  have hp (a b : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => dcoord (fun z => F z b) y a) :=
    contDiff_iff_contDiffAt.mpr (fun _ => partial_smooth (hF b).contDiffAt a)
  have hs (a b c d : Fin 3) :
      ‖iteratedFDeriv ℝ j (fun y => dcoord (fun z => F z b) y a-dcoord (fun z => F z d) y c) x‖ ≤ 2*A :=
    (sub_jet_bound _ _ (hp a b) (hp c d) j x).trans
      ((add_le_add ((partial_jet_bound _ (hF b) j x a).trans (hb b))
        ((partial_jet_bound _ (hF d) j x c).trans (hb d))).trans_eq (by ring))
  fin_cases i
  · exact hs 1 2 2 1
  · exact hs 2 0 0 2
  · exact hs 0 1 1 0

theorem radial_vector_jet_bound (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (N j : ℕ) (hj : j≤N) (x : Space) (b A : ℝ) (hA : 0≤A) (hx : ‖x‖≤b)
    (hjet : ∀ a, a≤N → ‖iteratedFDeriv ℝ a f x‖≤A) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => radialVector f y i) x‖≤2^N*max 1 b*A := by
  exact PolynomialJetBounds.mul_jet_bound _ _ N j x (max 1 b) A
    (le_trans (by norm_num) (le_max_left _ _)) hA (ScalarExterior.coordinateCLM i).contDiff hf
    (fun a _ => PolynomialJetBounds.coordinate_jet_bound i a x _ (le_max_left _ _)
      (hx.trans (le_max_right _ _))) hjet hj

theorem regular_vector_jets (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (N j : ℕ) (hj : j≤N) (x : Space) (b A : ℝ) (hA : 0≤A) (hx : ‖x‖≤b)
    (hjet : ∀ a, a≤N+2 → ‖iteratedFDeriv ℝ a f x‖≤A) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => toroidal f y i) x‖≤4*2^(N+2)*max 1 b*A ∧
    ‖iteratedFDeriv ℝ j (fun y => DebyeMaxwell.tmElectric f y i) x‖≤4*2^(N+2)*max 1 b*A := by
  let D := 2^(N+2)*max 1 b*A
  have hD : 0≤D := by dsimp [D]; positivity
  have hrad (a : ℕ) (ha : a≤N+2) (i : Fin 3) :
      ‖iteratedFDeriv ℝ a (fun y => radialVector f y i) x‖≤D :=
    radial_vector_jet_bound f hf (N+2) a ha x b A hA hx hjet i
  have hr (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => radialVector f y i) :=
    contDiff_iff_contDiffAt.mpr (fun y => radialVector_smooth f y hf.contDiffAt i)
  have ht (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => toroidal f y i) :=
    contDiff_iff_contDiffAt.mpr (fun y => toroidal_smooth f y hf.contDiffAt i)
  have hb (a : ℕ) (ha : a≤N+1) (i : Fin 3) :
      ‖iteratedFDeriv ℝ a (fun y => toroidal f y i) x‖≤2*D :=
    curl_jet_bound _ hr a x D (hrad (a+1) (by omega)) i
  constructor
  · have h := hb j (by omega) i
    dsimp [D] at *
    nlinarith
  · have h := curl_jet_bound (toroidal f) ht j x (2*D) (hb (j+1) (by omega)) i
    convert h using 1
    dsimp [D]
    ring

def scale (N : ℕ) (b : ℝ) : ℝ := 4*2^(N+2)*max 1 b*lowerJetScale 1 (N+2) b

theorem scale_nonnegative (N : ℕ) (b : ℝ) (hb : 0≤b) : 0≤scale N b := by
  have h := lowerJetScale_nonnegative 1 (N+2) b hb
  dsimp [scale]
  positivity

theorem normalized_vector_jet_bound (l : ℕ) (m : Index l) (N j : ℕ) (hj : j≤N)
    (b B : ℝ) (hb : 0≤b) (hB : 0≤B) (hbB : degreeScale (N+2) b≤B)
    (x : Space) (hx : ‖x‖≤b) (i : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => toroidal (SolidScalarHelmholtz.wave l 1 (representative l m)) y i) x‖≤
      scale N b*amplitude l 0*(l+1 : ℝ)^3*B^l ∧
    ‖iteratedFDeriv ℝ j (fun y => DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l 1 (representative l m)) y i) x‖≤
      scale N b*amplitude l 0*(l+1 : ℝ)^3*B^l := by
  let A := lowerJetScale 1 (N+2) b*amplitude l 0*(l+1 : ℝ)^3*B^l
  have hA : 0≤A := by
    have h := lowerJetScale_nonnegative 1 (N+2) b hb
    have h' := (amplitude_pos l 0).le
    dsimp [A]
    positivity
  have hjet (a : ℕ) (ha : a≤N+2) :
      ‖iteratedFDeriv ℝ a (SolidScalarHelmholtz.wave l 1 (representative l m)) x‖≤A := by
    apply (normalized_wave_enlarged_bound l m 1 a b B hb ((degreeScale_mono (N+2) a b ha).trans hbB) x hx).trans
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (jetScale_le_lowerJetScale 1 (N+2) a b hb ha)
        (amplitude_pos l 0).le) (by positivity)) (pow_nonneg hB _)
  have h := regular_vector_jets _ (SolidScalarHelmholtz.wave_contDiff l 1 _) N j hj x b A hA hx hjet i
  constructor
  · exact h.1.trans_eq (by dsimp [scale,A]; ring)
  · exact h.2.trans_eq (by dsimp [scale,A]; ring)

end OQ14.DebyeJetBounds
#print axioms OQ14.DebyeJetBounds.partial_jet_bound
#print axioms OQ14.DebyeJetBounds.sub_jet_bound
#print axioms OQ14.DebyeJetBounds.curl_jet_bound
#print axioms OQ14.DebyeJetBounds.radial_vector_jet_bound
#print axioms OQ14.DebyeJetBounds.regular_vector_jets
#print axioms OQ14.DebyeJetBounds.scale_nonnegative
#print axioms OQ14.DebyeJetBounds.normalized_vector_jet_bound
