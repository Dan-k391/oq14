import Packet06SphereInsertionMode
import ConicalFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ModalConeBranch
open Set Metric Filter OQ14.Maxwell
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data

theorem cone_contrast_relative (n η t : ℝ) (x : Space) :
    n^2 + η * (ConicalCapField.permittivity (n^2) t x - 1) =
      n^2 * ConicalCapField.permittivity η t x := by
  classical
  unfold ConicalCapField.permittivity CapSturmLiouville.coefficient
  split_ifs <;> ring

theorem local_dielectric_match (n : ℝ) (hn : 1 < n) (p : Data) (a η : ℝ) (hη : 0 ≤ η)
    (hcontrast : p.contrast = n^2) (ha : a ≤ p.cutoff.rOut)
    (cone : StaticCoefficient.Coefficient) (center x : Space) (hx : ‖x-center‖ ≤ a) (hsphere : ‖x‖ < 1)
    (hlocal : cone.value (VectorFourier.coordinateMap x) =
      (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap (x-center))) :
    1 + (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) cone η hη).value
      (VectorFourier.coordinateMap x) = n^2 * ConicalCapField.permittivity η p.threshold (x-center) := by
  change 1 + ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) +
    η*cone.value (VectorFourier.coordinateMap x)) = _
  have hcone : cone.value (VectorFourier.coordinateMap x) =
      ConicalCapField.permittivity (n^2) p.threshold (x-center)-1 := by
    rw [hlocal,ConicalSeparatedSource.material_eq_inside p a _ hx,ConicalStaticVolume.coefficient_spatial]
    unfold ConicalAnnularSource.dielectric
    have hb : x-center ∈ closedBall (0 : Space) p.cutoff.rOut := by
      simp only [mem_closedBall,dist_zero_right]
      exact hx.trans ha
    simp [hb,hcontrast]
  rw [hcone,ModalWeightedMode.coefficient_value,if_pos hsphere]
  have h := cone_contrast_relative n η p.threshold (x-center)
  linarith

theorem positive_contrast_angular_branch (χ : ContDiffBump (0 : Space)) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) :
    ∃ p : ℕ → Data, ∀ j, (p j).cutoff = χ ∧ (p j).contrast = η j ∧
      (p j).threshold = t ∧ 0 < (p j).exponent ∧ (p j).exponent < 1 ∧
      CapAngularShooting.determinant (η j) t (p j).eigenvalue = 0 ∧
      ∃ S : Set AngularPower.Sphere, IsOpen S ∧ S.Nonempty ∧
        0 < AngularPower.angularMeasure S ∧
        ∀ M : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ q ∈ S,
          M < ‖ConicalCutoffGradient.cutElectric χ (p j).exponent (p j).eigenvalue t
            (r • (q : Space))‖ := by
  classical
  have h : ∀ j, ∃ p : Data, p.cutoff = χ ∧ p.contrast = η j ∧ p.threshold = t ∧ p.exponent < 1 := by
    intro j
    obtain ⟨p,hχ,hd,ht',hν,_⟩ := ConicalFamily.exists_data χ (η j) t (hη j) ht ht1
    exact ⟨p,hχ,hd,ht',hν⟩
  choose p hp using h
  refine ⟨p,?_⟩
  intro j
  obtain ⟨hχ,hd,ht',hν⟩ := hp j
  have hroot : CapAngularShooting.determinant (η j) t (p j).eigenvalue = 0 := by
    simpa only [hd,ht'] using (p j).angular_root
  obtain ⟨S,hS,hne,hm,hblow⟩ := ConicalFamily.localized_static_blowup (p j) hν
  refine ⟨hχ,hd,ht',(p j).exponent_pos,hν,hroot,S,hS,hne,hm,?_⟩
  simpa only [hχ,ht'] using hblow
#print axioms OQ14.Packet06ModalConeBranch.cone_contrast_relative
#print axioms OQ14.Packet06ModalConeBranch.local_dielectric_match
#print axioms OQ14.Packet06ModalConeBranch.positive_contrast_angular_branch
end OQ14.Packet06ModalConeBranch
