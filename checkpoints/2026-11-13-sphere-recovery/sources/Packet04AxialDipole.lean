import ModalAxialRotation
import PolarMomentAE
import SphereAngularSymmetry

/-! The proper half-turn kills both transverse degree-one radial moments of
every actual axial L² vector. This uses only almost-everywhere representatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04AxialDipole
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.ModalAxialRotation
  OQ14.HalfTurnVectorAction
abbrev Space := Maxwell.Space

theorem rotation_neg_pi (x : Space) : rotation (-Real.pi) x = rot x := by
  ext i
  fin_cases i <;> simp [rotation, spatial, rot_coordinate, o, SphereReactionKernel.sign]

theorem action_pi (u : VectorFourier.VectorL2) : action Real.pi u = U u := by
  apply vector_ext_pt
  intro i
  filter_upwards [action_ae Real.pi u i, U_ae u i] with x h1 h2
  rw [h1, h2, rotation_neg_pi]
  fin_cases i <;> simp [matrix, Fin.sum_univ_three, o, SphereReactionKernel.sign]

theorem axial_halfturn (u : VectorFourier.VectorL2) (hu : u ∈ axialSector) : U u = u := by
  simp only [axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hu
  rw [← action_pi]
  exact hu Real.pi

def radialScalar (u : VectorFourier.VectorL2) (x : Space) : ℂ :=
  ∑ j : Fin 3, (x j : ℂ) * u (VectorFourier.coordinateMap x) j

theorem radial_halfturn (u : VectorFourier.VectorL2) (hu : u ∈ axialSector) :
    (fun x => radialScalar u (rot x)) =ᵐ[volume] radialScalar u := by
  have he := ae_all_iff.mpr (fun j : Fin 3 => U_ae u j)
  filter_upwards [he] with x hx
  simp only [axial_halfturn u hu] at hx
  unfold radialScalar
  apply Finset.sum_congr rfl
  intro j _
  rw [rot_coordinate, Complex.ofReal_mul, hx j]
  ring

theorem transverse_weighted_moment_zero (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (i : Fin 3) (hi : i ≠ 2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      (∫ ω : Sphere, radialScalar u (r • (ω : Space)) * ((ω : Space) i : ℂ)
        ∂angularMeasure) = 0 := by
  filter_upwards [PolarMomentAE.polar_ae (radial_halfturn u hu)] with r hr
  let Q := SphereAngularSymmetry.sphereMap rot
  let f : Sphere → ℂ := fun ω => radialScalar u (r • (ω : Space)) * ((ω : Space) i : ℂ)
  have hp := (SphereAngularSymmetry.measurePreserving_sphereMap rot).integral_comp
    (SphereAngularSymmetry.sphereMap rot).measurableEmbedding f
  have he : (∫ ω : Sphere, f (Q ω) ∂angularMeasure) =
      -(∫ ω : Sphere, f ω ∂angularMeasure) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hr] with ω hω
    change radialScalar u (r • rot (ω : Space)) * (rot (ω : Space) i : ℂ) = _
    rw [← map_smul, hω, rot_coordinate]
    have ho : o i = -1 := by fin_cases i <;> simp_all [o, SphereReactionKernel.sign]
    simp only [ho, neg_one_mul, Complex.ofReal_neg, f]
    ring
  change (∫ ω : Sphere, f ω ∂angularMeasure) = 0
  change (∫ ω : Sphere, f (Q ω) ∂angularMeasure) = ∫ ω : Sphere, f ω ∂angularMeasure at hp
  linear_combination (he - hp) / 2

end OQ14.Packet04AxialDipole
#print axioms OQ14.Packet04AxialDipole.rotation_neg_pi
#print axioms OQ14.Packet04AxialDipole.action_pi
#print axioms OQ14.Packet04AxialDipole.axial_halfturn
#print axioms OQ14.Packet04AxialDipole.radial_halfturn
#print axioms OQ14.Packet04AxialDipole.transverse_weighted_moment_zero
